-- Prove2me | Theorems.Thm_ConvexOptimization_lowner_john_exists
-- name    : ConvexOptimization.lowner_john_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T04:09:49.23041+00:00
-- url     : https://prove2.me/theorems/02463ebb-0c4e-42b4-abf0-4a5abcc636ad
-- title:
--   Existence of the Löwner–John ellipsoid
-- statement:
--   Existence of the minimum-volume covering ellipsoid for a finite, full-dimensional point set.
--
--   Let $x_1, \dots, x_m \in \mathbb{R}^n$ and let $C = \operatorname{conv}\{x_1,\dots,x_m\}$ be their convex hull. Assume $C$ has nonempty interior, i.e. the points are not contained in any proper affine subspace of $\mathbb{R}^n$. Then a Löwner–John pair exists:
--
--   $$\exists\, A = A^{T} \succ 0,\ b \in \mathbb{R}^n \ : \quad \{x_1,\dots,x_m\} \subseteq \mathcal{E}(A,b) \quad\text{and}\quad \det A' \le \det A \ \text{ for every covering pair } (A',b'),$$
--
--   where $\mathcal{E}(A,b) = \{v : \lVert Av+b\rVert_2 \le 1\}$.
--
--   The result says the supremum of $\det A$ over covering pairs is attained, so that all later statements may speak of *the* minimum-volume covering ellipsoid rather than of an infimum. Full-dimensionality is not a technicality: if the points lie in a hyperplane, a covering ellipsoid can be stretched arbitrarily far in the orthogonal direction without losing the covering property, $\det A$ is unbounded above, and no extremal pair exists.
--
--   **Formalization Note** The points are given as a family `x : Fin m → (Fin n → ℝ)` and the covering condition is imposed on its range; this is equivalent to covering $C$, since ellipsoids are convex. Full-dimensionality is expressed as `(interior (convexHull ℝ (Set.range x))).Nonempty`. Boyd & Vandenberghe pose problem (8.12) without a separate existence argument, so this statement is supplied by the mission.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 411, §8.4.1 eq. (8.11) (the minimum volume covering ellipsoid of a finite point set). Attainment is presumed rather than proved in the book; the compactness argument is supplied by this mission

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lowner_john_exists {nn m : ℕ} (x : Fin m → Fin nn → ℝ)
    (hfull : (interior (convexHull ℝ (Set.range x))).Nonempty) :
    ∃ (A : Matrix (Fin nn) (Fin nn) ℝ) (b : Fin nn → ℝ),
      IsLownerJohn A b (Set.range x) := by
  sorry
