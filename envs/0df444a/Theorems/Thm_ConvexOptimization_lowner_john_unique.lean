-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_unique
-- name    : ConvexOptimization.lowner_john_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:10:21.990911+00:00
-- url     : https://prove2.me/theorems/a6bfd96a-ac54-4ac6-b631-717b658aaf5f
-- title:
--   Uniqueness of the Löwner–John ellipsoid
-- statement:
--   Uniqueness of the Löwner–John ellipsoid, at the level of its parametrizing pair.
--
--   Let $x_1, \dots, x_m \in \mathbb{R}^n$ and suppose $(A_1, b_1)$ and $(A_2, b_2)$ are both Löwner–John pairs for $\{x_1,\dots,x_m\}$ — each symmetric positive definite, covering, and of maximal determinant among covering pairs. Then
--
--   $$A_1 = A_2 \qquad\text{and}\qquad b_1 = b_2 .$$
--
--   Together with existence, this licenses the phrase *the* minimum-volume covering ellipsoid and makes the affine-invariance and rounding statements well posed: the ellipsoid attached to a point set is a genuine function of the set, so normalizing a configuration by an affine change of coordinates is unambiguous.
--
--   No full-dimensionality hypothesis is needed here, because it is already implied: for a point set contained in a proper affine subspace no maximal covering pair exists, so the hypotheses are vacuous in that case.
--
--   **Formalization Note** The conclusion identifies the parameters, which is stronger than identifying the sets $\mathcal{E}(A_1,b_1) = \mathcal{E}(A_2,b_2)$; it is the symmetry-plus-positive-definiteness normalization inside the Löwner–John predicate that makes the parametrization rigid. Source: Boyd & Vandenberghe, exercise 8.12.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 449, exercise 8.12 (show that the Loewner-John ellipsoid of a set is unique)

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_unique {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (A₁ A₂ : Matrix (Fin nn) (Fin nn) ℝ) (b₁ b₂ : Fin nn → ℝ)
    (h₁ : IsLownerJohn A₁ b₁ (Set.range x))
    (h₂ : IsLownerJohn A₂ b₂ (Set.range x)) :
    A₁ = A₂ ∧ b₁ = b₂ := by
  sorry
