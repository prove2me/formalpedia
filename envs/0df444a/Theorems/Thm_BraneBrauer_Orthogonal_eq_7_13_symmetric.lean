-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_eq_7_13_symmetric
-- name    : BraneBrauer.Orthogonal.eq_7_13_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:34.861371+00:00
-- url     : https://prove2.me/theorems/60666ffc-38e8-4100-9146-b921ceddb626
-- title:
--   (7.13), third line — symmetric permutation sum
-- statement:
--   Suppose $Y_1,Y_2$ are operators invariant under conjugation by every tensor permutation in $S_m\times S_n$. Then
--   $$
--   \langle\Sigma(Y_2),\Sigma(Y_1)\rangle
--   =m!n!\operatorname{tr}_{m,n}
--   \bigl((\Sigma Y_2)^\dagger\Sigma Y_1\bigr).
--   $$
--   For symmetric branching operators, all terms of the Wick sum coincide, giving the normalization in the third line of (7.13).
--
--   **Formalization Note** Both operators are required to satisfy the symmetry stated in §7. The formula is stated for all such operators, rather than only the particular branching family.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 29, (7.13), third line

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section
open Matrix

namespace BraneBrauer.Orthogonal

/-- (7.13), third line, p. 29: for symmetric branching operators,
the permutation sum has `m!n!` identical terms. -/
theorem eq_7_13_symmetric {N m n : ℕ} (Y₂ Y₁ : Op N m n)
    (h₂ : ∀ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)),
      permOp N m n σ τ * Y₂ * permOp N m n σ⁻¹ τ⁻¹ = Y₂)
    (h₁ : ∀ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)),
      permOp N m n σ τ * Y₁ * permOp N m n σ⁻¹ τ⁻¹ = Y₁) :
    innerProd N m n (sigma Y₂) (sigma Y₁) =
      ((m.factorial * n.factorial : ℕ) : ℂ) *
        ((sigma Y₂)ᴴ * sigma Y₁).trace := by sorry

end BraneBrauer.Orthogonal
