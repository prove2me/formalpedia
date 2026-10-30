-- Prove2me | Theorems.Thm_DerivativeChainPrivate_affine_orthonormal_coordinates
-- name    : DerivativeChainPrivate.affine_orthonormal_coordinates
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:56:49.317979+00:00
-- url     : https://prove2.me/theorems/5870efe4-86b7-4cc4-8caf-6ab04e6edff4
-- title:
--   Orthonormal monotone coordinates survive a nonzero affine map
-- statement:
--   Let a finite complex list $z$ have nondecreasing projections along unit coefficients $a,b$ with $\operatorname{Re}(a\overline b)=0$. For arbitrary $t,c\in\mathbb C$ with $c\ne0$, the list $t+cz_i$ has nondecreasing projections along some unit orthogonal coefficients $A,B$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L1637-L1682

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.affine_orthonormal_coordinates {n : ℕ} (z : Fin n → ℂ) (a b t c : ℂ)
    (hc : c ≠ 0) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : (a*starRingEnd ℂ b).re = 0)
    (hmonoA : Monotone (fun i => (a*z i).re))
    (hmonoB : Monotone (fun i => (b*z i).re)) :
    ∃ A B : ℂ, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*(t+c*z i)).re) ∧ Monotone (fun i => (B*(t+c*z i)).re) := by sorry
