-- Prove2me | Theorems.Thm_DetDLP_d4_small_regime_terminal_machine
-- name    : DetDLP.d4_small_regime_terminal_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:55:56.758815+00:00
-- url     : https://prove2.me/theorems/a32c6b94-bf5e-4edb-adfe-23ae7463bdb6
-- title:
--   Polynomial terminal machine below a fixed logarithmic threshold
-- statement:
--   For each fixed threshold and fixed entry evaluator, a uniform primitive machine computes the canonical coefficient word whenever the ceiling base-two logarithm of the core size is below that threshold. Both time and space are polynomial in the core size plus the descriptor length.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_small_regime_terminal_machine (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) (L₀ : ℕ) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (K : ℕ), ∀ x : Input C c,
      Nat.clog 2 x.S < L₀ → entry x E o → RunsWithin M om (input x) (answer x) (polyBound K (size x)) (polyBound K (size x)) := by sorry
