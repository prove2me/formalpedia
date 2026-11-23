-- Prove2me | Theorems.Thm_Arm64Facts_steps_codeLoaded
-- name    : Arm64Facts.steps_codeLoaded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-23T11:20:39.413948+00:00
-- url     : https://prove2.me/theorems/93ac6f06-df15-4dc2-b1d7-da292808d4e0
-- title:
--   AArch64 execution keeps loaded code loaded
-- statement:
--   In the published AArch64 semantics (bundle `Arm64_ISA_Semantics`): if `Steps prog s s'` (the program `prog` runs from state $s$ to state $s'$ in finitely many steps) and the code of some program `prog'` is loaded in the memory of $s$ (`prog'.CodeLoaded s.mem`: its bytes are at `prog'.base`, mapped read-execute, not lazily freed, and the image is aligned and does not wrap), then the code of `prog'` is still loaded in the memory of $s'$.
--
--   The two programs may differ: `prog'` can be any program whose code is in memory, for instance another block of a library that `prog` calls into. The reason is that loaded code is mapped read-execute and so is frozen: instruction stores only write bytes that are writable and not executable, supervisor calls restore every frozen byte, and the semantics lets an extern hook take effect only when it keeps frozen bytes. This is DeepMind's `Steps.codeLoaded` (google-deepmind/code-verification @ 8c8d371f, `arm64-semantics/ProofLib/Invariant.lean`), which follows from their `Steps.keepsFrozen`. It is the fact a proof needs to continue executing its own code after a call into another function returns.
-- source:
--   google-deepmind/code-verification @ 8c8d371f (Apache-2.0), arm64-semantics/ProofLib/Invariant.lean, theorem Steps.codeLoaded, https://github.com/google-deepmind/code-verification

import Mathlib
import Definitions.Def_Arm64_ISA_Semantics

namespace Arm64Facts

open Arm64

theorem steps_codeLoaded {prog prog' : Program} {s s' : State} (h : Steps prog s s')
    (hL : prog'.CodeLoaded s.mem) : prog'.CodeLoaded s'.mem := by
  sorry

end Arm64Facts
