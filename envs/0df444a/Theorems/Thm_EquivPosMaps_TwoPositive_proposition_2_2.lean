-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_proposition_2_2
-- name    : EquivPosMaps.TwoPositive.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:45.66529+00:00
-- url     : https://prove2.me/theorems/bb74eb6e-2d9d-4cd9-9a60-9b9aaeba1a5e
-- title:
--   Proposition 2.2: block criterion for k-positivity
-- statement:
--   Let $\Psi:M_{d_1}(\mathbb C)\to M_{d_2}(\mathbb C)$ be a Hermitian-preserving complex-linear map. Assume that for every unitary $U$ there is a matrix $V$ such that $\Psi(UXU^*)=V\Psi(X)V^*$ for every $X$. For $k\leq\min(d_1,d_2)$, form the block matrix $[\Psi(e_{ij})]_{i,j=1}^k$. Then
--
--   $$\Psi\text{ is }k\text{-positive}\quad\Longleftrightarrow\quad[\Psi(e_{ij})]_{i,j=1}^k\geq0.$$
--
--   This reduces the universal condition in $k$-positivity to one finite matrix inequality for maps with the paper's equivariance property.
--
--   **Formalization Note** “Self adjoint” is represented as preservation of conjugate transpose, $\Psi(X^*)=\Psi(X)^*$, rather than self adjointness as an operator on a Hilbert space. The paper's bound $k\leq d_2$ is retained.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, p. 4, Proposition 2.2

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Proposition 2.2, p. 4: the first k Choi blocks characterize k-positivity under equivariance. -/
theorem proposition_2_2 (d₁ d₂ k : ℕ)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (hself : ∀ X : Matrix (Fin d₁) (Fin d₁) ℂ, Φ Xᴴ = (Φ X)ᴴ)
    (hequiv : ∀ U : Matrix.unitaryGroup (Fin d₁) ℂ,
      ∃ V : Matrix (Fin d₂) (Fin d₂) ℂ, ∀ X : Matrix (Fin d₁) (Fin d₁) ℂ,
        Φ ((U : Matrix (Fin d₁) (Fin d₁) ℂ) * X * star (U : Matrix (Fin d₁) (Fin d₁) ℂ)) =
          V * Φ X * Vᴴ)
    (hk : k ≤ min d₁ d₂) :
    KPositive k Φ ↔ (blockMatrix k (le_min_iff.mp hk).1 Φ).PosSemidef := by sorry

end EquivPosMaps.TwoPositive
