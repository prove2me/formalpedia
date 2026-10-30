-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_covariance_nested
-- name    : DerivativeChainContinuation.actual_covariance_nested
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:35:37.774021+00:00
-- url     : https://prove2.me/theorems/c671c677-af0d-4d42-a629-7e32699e09d7
-- title:
--   Positive semidefinite covariance nesting
-- statement:
--   For a centered monic complex polynomial $p$ of degree $n+3$, and its monic derivative $q$, $$\frac{\Sigma(p)}{n+2}-\frac{\Sigma(q)}{n+1}\succeq0.$$ Covariances are formed from actual derivative-root multisets.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitComplete.lean#L8-L14

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

theorem DerivativeChainContinuation.actual_covariance_nested (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hc : p.roots.sum = 0) :
    (((n+2 : ℝ)⁻¹ • rootCovariance p) -
      ((n+1 : ℝ)⁻¹ • rootCovariance (monicDerivative p))).PosSemidef := by sorry
