-- Prove2me | Theorems.Thm_DetDLP_d4_partial_unroll_rank_enumerator_v2
-- name    : DetDLP.d4_partial_unroll_rank_enumerator_v2
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T06:45:49.81594+00:00
-- url     : https://prove2.me/theorems/f9049b79-4672-4c03-8ceb-325ceed96140
-- title:
--   Counted terminal partial unrolling with a recoverable modulus
-- statement:
--   Each branch header uses a monic modulus with binary coefficients below its leading term, so its polynomial bit word identifies the modulus. The ranked residual plans obey the count, geometry, guarded coefficient, and uniform source-evaluation contracts.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_partial_unroll_rank_enumerator_v2 (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K L₀ : ℕ) (P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x),
      (∀ x hl he, ∀ i < (P x hl he).f.natDegree, (P x hl he).f.coeff i = 0 ∨ (P x hl he).f.coeff i = 1) ∧
      (∀ x hl he, Enumerates A oa K (P x hl he)) ∧
      (AppendixD4.Closed → ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ), ∀ x hl he, Sources B ob k (P x hl he)) := by sorry
