-- Prove2me | Theorems.Thm_DerivativeChainContinuation_derivative_covariance_rescaling
-- name    : DerivativeChainContinuation.derivative_covariance_rescaling
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:11:33.865626+00:00
-- url     : https://prove2.me/theorems/b0d8523f-59e8-45c6-9604-0632e3e15303
-- title:
--   Exact covariance rescaling for an actual derivative
-- statement:
--   Let $p$ be monic and centered of degree $n+3$, and $q$ its monic normalized derivative. Write $\Sigma(p)$ for its uniform real root covariance and $\delta(p)=(n+1)V(p)-(n+2)V(q)$ for its Schoenberg deficit. Then $$\frac{\Sigma(p)}{n+2}-\frac{\Sigma(q)}{n+1}=\frac{\delta(p)}{2(n+2)(n+1)}I_2.$$ Root slots retain multiplicity.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RowCovariance.lean#L38-L57

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.derivative_covariance_rescaling (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    ((n+2 : ℝ)⁻¹ • rootCovariance p) -
      ((n+1 : ℝ)⁻¹ • rootCovariance (monicDerivative p)) =
      (schoenbergDeficit p / (2*(n+2)*(n+1) : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
