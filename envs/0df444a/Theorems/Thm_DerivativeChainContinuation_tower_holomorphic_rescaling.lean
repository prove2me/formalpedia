-- Prove2me | Theorems.Thm_DerivativeChainContinuation_tower_holomorphic_rescaling
-- name    : DerivativeChainContinuation.tower_holomorphic_rescaling
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:37:31.979382+00:00
-- url     : https://prove2.me/theorems/f3067e2d-92ec-41ad-8c15-0460b2ccc8ec
-- title:
--   Holomorphic second moment along an actual derivative tower
-- statement:
--   Let $P_2,\ldots,P_{n+2}$ be centered monic complex polynomials of the indicated degrees, with each lower row the monic normalized derivative of the next. Their uniform complex second moments satisfy $$H(P_2)=\frac{H(P_{n+2})}{n+1}.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TowerBudget.lean#L7-L24

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

theorem DerivativeChainContinuation.tower_holomorphic_rescaling (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    rootHolomorphicMoment (P 2) = rootHolomorphicMoment (P (n+2))/(n+1 : ℂ) := by sorry
