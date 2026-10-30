-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_tower_weighted_determinant_bound
-- name    : DerivativeChainContinuation.actual_tower_weighted_determinant_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:00:58.038508+00:00
-- url     : https://prove2.me/theorems/f0bec13e-105e-4100-ad66-6ca5fb4d5bc5
-- title:
--   Weighted covariance determinant bound for an actual tower
-- statement:
--   Let $P_2,\ldots,P_{n+2}$ be centered monic actual normalized derivative rows. Write $R_m$ for the largest root norm, $\Sigma_m$ for covariance and $\beta_m=(V_m-|H_m|)/2$ for transverse variance. Then $$\sum_{k=0}^{n-1}\frac{\det\Sigma_{k+3}}{R_{k+3}^2(k+2)(k+1)}\le\frac{4\beta_{n+2}}{n+1}.$$ Zero-radius summands use totalized division. This is C5.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitInequalities.lean#L47-L74

import Mathlib
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RootCovariance
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.actual_tower_weighted_determinant_bound (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    (∑ k ∈ Finset.range n,
      (rootCovariance (P (k+3))).det/
        ((rootRadius (P (k+3)))^2*(k+2 : ℕ)*(k+1 : ℕ))) ≤
      4*transverseVariance (P (n+2))/(n+1 : ℕ) := by sorry
