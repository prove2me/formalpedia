-- Prove2me | Theorems.Thm_DetDLP_d4_stopped_source_evaluator_machine
-- name    : DetDLP.d4_stopped_source_evaluator_machine
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T07:16:32.676426+00:00
-- url     : https://prove2.me/theorems/41bd71d0-4ae8-448d-8785-f2d1cc4d81f5
-- title:
--   Uniform stopped-source evaluator
-- statement:
--   Under the closed-schedule contraction hypothesis, construct one source machine evaluating every tensor entry in each guarded residual Plan.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_stopped_source_evaluator_machine (C c : ℕ) (hC : 0 < C) (hc : 0 < c)
    (E : PrimitiveMachine) (o : Fin E.tapeCount) (L₀ : ℕ) (P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x) :
    AppendixD4.Closed → ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ),
      ∀ x hl he, Sources B ob k (P x hl he) := by sorry
