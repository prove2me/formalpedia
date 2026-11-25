-- Prove2me | Theorems.Thm_DetDLP_d4_core_cut_and_unroll_tree_math
-- name    : DetDLP.d4_core_cut_and_unroll_tree_math
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T07:16:15.010775+00:00
-- url     : https://prove2.me/theorems/d7e5ad98-e987-405c-befc-53b7a4636634
-- title:
--   D4 core cut and unroll-tree mathematics
-- statement:
--   For each input, construct a guarded residual Plan for the cut core and its stopped recursive expansion, with binary coefficients for its modulus polynomial.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_core_cut_and_unroll_tree_math (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ L₀ : ℕ, ∃ P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x,
      ∀ x hl he, ∀ i < (P x hl he).f.natDegree, (P x hl he).f.coeff i = 0 ∨ (P x hl he).f.coeff i = 1 := by sorry
