-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_orthogonality_7_12
-- name    : BraneBrauer.Orthogonal.orthogonality_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:32.146961+00:00
-- url     : https://prove2.me/theorems/4b923a35-1b78-4231-bcb0-d83a00edd667
-- title:
--   (7.12) — orthogonality of symmetric Brauer branching states
-- statement:
--   Fix $N,m,n\ge0$, branching labels $\gamma$ and $A$, multiplicities $M^\gamma_A$, and a system $Q^\gamma_{A,ij}$ of symmetric represented Brauer matrix units. Every index below lies in its multiplicity range. The polynomial states associated with $\Sigma(Q)$ satisfy
--   $$
--   \left\langle\Sigma(Q^{\gamma_2}_{A_2,i_2j_2}),
--   \Sigma(Q^{\gamma_1}_{A_1,i_1j_1})\right\rangle
--   =m!n!\,\delta_{\gamma_1\gamma_2}\delta_{A_1A_2}
--   \delta_{i_1i_2}\delta_{j_1j_2}
--   \operatorname{tr}_{m,n}(Q^{\gamma_1}_{A_1,j_1j_1}).
--   $$
--   Hence distinct branching labels or indices give orthogonal states in the two-matrix quantum-mechanical inner product.
--
--   **Formalization Note** The paper's coefficient is $d_{A_1}\operatorname{Dim}\gamma_1$. Here it is the equal trace $\operatorname{tr}_{m,n}(Q^{\gamma_1}_{A_1,j_1j_1})$; identifying the two is the omitted Schur–Weyl step (3.8), last line of (7.13). The Fock vacuum pairing is represented by an independent-entry Gaussian integral. $Q$ is characterized by Brauer membership, symmetry, matrix-unit multiplication, and its adjoint relation, without a completeness assumption.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 29, (7.12) and (7.13), last line

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section

namespace BraneBrauer.Orthogonal

/-- (7.12), p. 29: symmetric Brauer branching operators diagonalise
the two-matrix quantum-mechanical inner product. -/
theorem orthogonality_7_12 {N m n : ℕ} {Γ Λ : Type*}
    [DecidableEq Γ] [DecidableEq Λ]
    (M : Γ → Λ → ℕ) (Q : Γ → Λ → ℕ → ℕ → Op N m n)
    (hQ : IsBranchingSystem N m n M Q)
    (γ₁ γ₂ : Γ) (A₁ A₂ : Λ) (i₁ j₁ i₂ j₂ : ℕ)
    (hi₁ : i₁ < M γ₁ A₁) (hj₁ : j₁ < M γ₁ A₁)
    (hi₂ : i₂ < M γ₂ A₂) (hj₂ : j₂ < M γ₂ A₂) :
    innerProd N m n (sigma (Q γ₂ A₂ i₂ j₂))
      (sigma (Q γ₁ A₁ i₁ j₁)) =
    ((m.factorial * n.factorial : ℕ) : ℂ) *
      (if γ₁ = γ₂ ∧ A₁ = A₂ ∧ i₁ = i₂ ∧ j₁ = j₂
       then (Q γ₁ A₁ j₁ j₁).trace else 0) := by sorry

end BraneBrauer.Orthogonal
