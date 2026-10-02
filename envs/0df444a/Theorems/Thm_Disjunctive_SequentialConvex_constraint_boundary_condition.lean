-- Prove2me | Theorems.Thm_Disjunctive_SequentialConvex_constraint_boundary_condition
-- name    : Disjunctive.SequentialConvex.constraint_boundary_condition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:26:24.952527+00:00
-- url     : https://prove2.me/theorems/1a7272c9-cd51-4642-8f11-45f00c6effc8
-- title:
--   Theorem 3.3 — the constraint boundary condition
-- statement:
--   This is Theorem 3.3 of Balas's *Disjunctive Programming*: the exact necessary and sufficient
--   condition for the sequential-convexification step to be valid at a single stage, sharpening
--   Theorem 3.1's sufficient (but not necessary) faciality condition.
--
--   Write $D_j := \bigvee_{i \in Q_j}(d_i x \ge d_{i0})$ and $\bar D_j := \bigvee_{i \in
--   Q_j}(d_i x \le d_{i0})$. Relation (3.5), the fact the sequential procedure needs at every
--   stage, is
--
--   $$
--   \mathrm{conv}\big[(\mathrm{conv}\,F_{j-1}) \cap D_j\big] = \mathrm{conv}(F_{j-1} \cap D_j).
--   $$
--
--   Theorem 3.3 shows (3.5) holds if and only if the **constraint boundary condition** holds: for
--   every $x \in F_{j-1} \cap \bar D_j$ and $y \in F_{j-1} \cap D_j$, every point where the segment
--   $[x,y]$ crosses the boundary of $\bar D_j$ (relative to the affine space it spans) already lies
--   in $\mathrm{conv}(F_{j-1} \cap D_j)$. The "if" direction is the substantive one: it says it
--   suffices to check only those boundary points reachable as a convex combination of *two* points
--   of $F_{j-1}$, rather than checking (3.5) directly against all of $\mathrm{conv}(F_{j-1})$.
--
--   **Formalization Note.** `intrinsicFrontier ℝ` is Mathlib's boundary relative to a set's own
--   affine span, matching "the boundary of $\bar D_j$ in the affine space spanned by $\bar D_j$"
--   exactly; `segment ℝ x y` is the closed line segment $[x,y]$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 46, Theorem 3.3

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

namespace Disjunctive.SequentialConvex

/-- Theorem 3.3 (Balas §3.2, p. 46): `F_{j-1}` and `D_j` satisfy the sequential-convexifiability
relation (3.5) if and only if they satisfy the constraint boundary condition (3.6): every point
where a segment from `F_{j-1} ∩ D̄_j` to `F_{j-1} ∩ D_j` crosses the (relative) boundary of `D̄_j`
lies in `conv(F_{j-1} ∩ D_j)`. -/
theorem constraint_boundary_condition {n : ℕ} (Fjm1 : Set (Fin n → ℝ)) {Qj : Type*} [Fintype Qj]
    (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    (convexHull ℝ (convexHull ℝ Fjm1 ∩ Dj d d0) = convexHull ℝ (Fjm1 ∩ Dj d d0)) ↔
      (∀ x ∈ Fjm1 ∩ Dbarj d d0, ∀ y ∈ Fjm1 ∩ Dj d d0,
        segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (Fjm1 ∩ Dj d d0)) := by sorry

end Disjunctive.SequentialConvex
