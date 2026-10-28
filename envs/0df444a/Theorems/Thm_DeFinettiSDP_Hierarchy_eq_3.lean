-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_eq_3
-- name    : DeFinettiSDP.Hierarchy.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:44.974024+00:00
-- url     : https://prove2.me/theorems/5111df82-4455-4a43-a1f5-619908dd8b87
-- title:
--   Eq. (3), p. 2 — Q equals the maximum of the objective over mixtures Σ pᵢ W_Aⁱ ⊗ W_Bⁱ of feasible product states
-- statement:
--   For the constrained bilinear program
--
--   $$Q=\max\ \mathrm{Tr}[G_{AB}(W_A\otimes W_B)]\quad\text{s.t. } W_A,W_B\ \text{states},\ \Lambda_{A\to C_A}(W_A)=X_{C_A},\ \Gamma_{B\to C_B}(W_B)=Y_{C_B},$$
--
--   the optimal value is unchanged when one optimises over the convex hull of the feasible product points:
--
--   $$Q=\max\ \mathrm{Tr}\Big[G_{AB}\Big(\sum_{i\in I}p_iW_A^i\otimes W_B^i\Big)\Big]$$
--
--   over finite probability vectors $p$ and states $W_A^i$, $W_B^i$ with $\Lambda_{A\to C_A}(W_A^i)=X_{C_A}$ and $\Gamma_{B\to C_B}(W_B^i)=Y_{C_B}$ for every $i$.
--
--   This is how the de Finetti approximant, a mixture rather than a product, is compared with $Q$ in the proof of Theorem 3.1.
--
--   **Formalization Note** Both maxima are suprema (`sSup`) of the sets of objective values, with objective the real part of the trace (see the definition file). If there is no feasible pair, both sets are empty and both sides are $0$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §1, eq. (3), p. 2 (the sentence begins on p. 1)

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Problem
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Eq. (3)** (arXiv:1810.12197v3, p. 2). The optimal value `Q` of the constrained bilinear
program (2) equals the optimal value of the same objective over the convex hull of feasible
points: mixtures `∑_i p_i W_A^i ⊗ W_B^i` of feasible product states. -/
theorem eq_3 {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) :
    Qval G Λ Γ X Y = sSup (Qmixset G Λ Γ X Y) := by sorry

end DeFinettiSDP.Hierarchy
