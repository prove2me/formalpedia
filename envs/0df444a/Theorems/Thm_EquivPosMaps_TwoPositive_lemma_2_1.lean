-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_lemma_2_1
-- name    : EquivPosMaps.TwoPositive.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:40.903072+00:00
-- url     : https://prove2.me/theorems/fd4867b1-8293-4c40-814a-adec8be376e6
-- title:
--   Lemma 2.1: equivariance and one matrix unit imply positivity
-- statement:
--   Let $\Psi:M_{d_1}(\mathbb C)\to M_{d_2}(\mathbb C)$ be complex-linear, with $d_1\geq1$. Suppose that for every unitary $U\in M_{d_1}(\mathbb C)$ there is a matrix $V\in M_{d_2}(\mathbb C)$ such that $\Psi(UXU^*)=V\Psi(X)V^*$ for every $X$. If $\Psi(e_{11})\geq0$, then
--
--   $$\Psi(X)\geq0\quad\text{for every }X\geq0.$$
--
--   The lemma is the paper's positivity criterion for equivariant maps. The output matrix $V$ need not be unitary.
--
--   **Formalization Note** The condition $d_1\geq1$ makes the paper's $e_{11}$ a valid matrix unit; Lean uses index zero for that unit.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 4, Lemma 2.1

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Lemma 2.1, p. 4: equivariance and positivity on e₁₁ imply positivity. -/
theorem lemma_2_1 (d₁ d₂ : ℕ) [NeZero d₁]
    (Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (hequiv : ∀ U : Matrix.unitaryGroup (Fin d₁) ℂ,
      ∃ V : Matrix (Fin d₂) (Fin d₂) ℂ, ∀ X : Matrix (Fin d₁) (Fin d₁) ℂ,
        Φ ((U : Matrix (Fin d₁) (Fin d₁) ℂ) * X * star (U : Matrix (Fin d₁) (Fin d₁) ℂ)) =
          V * Φ X * Vᴴ)
    (hunit : (Φ (Matrix.single 0 0 1)).PosSemidef) :
    IsPositiveMap Φ := by sorry

end EquivPosMaps.TwoPositive
