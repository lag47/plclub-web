TUTORIAL:

  The main files for this tutorial are CoqIntro.v, STLC.v, and STLCsol.v.
  Before you start, run 'make' in this directory to compile the metatheory
  library, which is used by STLC.v and STLCsol.v.  If you don't have make,
  run the following commands.  (You may need to replace 'coqc' with the full
  path to the executable.)

      coqc -q -I . AdditionalTactics.v
      coqc -q -I . Atom.v
      coqc -q -I . FSetWeakDecide.v
      coqc -q -I . FSetWeakNotin.v
      coqc -q -I . ListFacts.v
      coqc -q -I . AtomSet.v
      coqc -q -I . AssocList.v
      coqc -q -I . AtomEnv.v
      coqc -q -I . Metatheory.v

  Those new to Coq should start with CoqIntro.v, which is an introduction to
  using Coq.  Solutions to the exercises here are at the end of the file.

  After CoqIntro.v, the next part of the tutorial is STLC.v, an introduction
  to mechanizing programming language definitions with binding in Coq and
  how to reason about them.  Solutions to exercises here are in STLCsol.v.

  All other files and the remainder of this README file concern the
  metatheory library (the 2008-07-17 release) developed by the University of
  Pennsylvania PLClub.  See http://plclub.org/metalib/ for more information.

===========================================================================

DOCUMENTATION:

  The main documentation for this library, including installation
  instructions and Coq documentation, is available as a collection of HTML
  files.  Start by opening doc/index.html in a web browser.

SOURCE CODE LICENSE:

  This library is distributed under the terms of the MIT License, also known
  as the X11 License.  The terms of the license are stated below.
  Essentially, you are free to do as you please with this library as long as
  appropriate credit is given to the original developers.

THE MIT LICENSE, A.K.A. THE X11 LICENSE:

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.
