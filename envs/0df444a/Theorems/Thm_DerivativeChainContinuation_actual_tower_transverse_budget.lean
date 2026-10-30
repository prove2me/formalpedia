-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_tower_transverse_budget
-- name    : DerivativeChainContinuation.actual_tower_transverse_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:39:50.965442+00:00
-- url     : https://prove2.me/theorems/7b81fe6f-ccd5-4afe-bd47-c6f2f56b2fc4
-- title:
--   Exact transverse deficit budget for an actual tower
-- statement:
--   Let $P_2,\ldots,P_{n+2}$ be centered monic actual normalized derivative rows. With $V$ the uniform squared root norm, $H$ the uniform complex square, and $\delta$ the Schoenberg deficit, $$\sum_{k=0}^{n-1}\frac{\delta(P_{k+3})}{(k+2)(k+1)}=\frac{V(P_{n+2})-|H(P_{n+2})|}{n+1}.$$ This is the complete C2 telescoping identity.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TowerBudget.lean#L26-L53

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.actual_tower_transverse_budget (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    (∑ k ∈ Finset.range n,
      schoenbergDeficit (P (k+3))/((k+2 : ℕ)*(k+1 : ℕ) : ℝ)) =
      (rootVariance (P (n+2)) - ‖rootHolomorphicMoment (P (n+2))‖)/(n+1 : ℕ) := by sorry
