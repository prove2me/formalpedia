-- Prove2me | Theorems.Thm_DetDLP_d4_residual_digit_entry_machine
-- name    : DetDLP.d4_residual_digit_entry_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:56:13.164669+00:00
-- url     : https://prove2.me/theorems/ea3a6637-c2bc-4296-b959-d91d24cf9fd8
-- title:
--   Uniform digit entries from residual vertex oracles
-- statement:
--   A single primitive machine evaluates the digit-query tensor at a vertex by recovering its source descriptor and extracting the prescribed slice of its coefficient word. The time is polynomial times an exponential in the block width, and the workspace is polynomial in the scalar query size.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_residual_digit_entry_machine (C c k e : ℕ) (B A : PrimitiveMachine) (ob : Fin B.tapeCount) (oa : Fin A.tapeCount) :
    ∃ (D : PrimitiveMachine) (od : Fin D.tapeCount) (K : ℕ), ∀ {x : Input C c} (P : Plan x),
      Enumerates A oa e P → Sources B ob k P → Digits D od K P := by sorry
