-- Prove2me | Theorems.Thm_Disjunctive_Polarity_projection_extreme_rays
-- name    : Disjunctive.Polarity.projection_extreme_rays
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:15:57.994037+00:00
-- url     : https://prove2.me/theorems/041a1bdb-9ddc-42f2-9ab2-27c4992ad981
-- title:
--   Theorem 2.5 — projection via extreme rays
-- statement:
--   This is Theorem 2.5 of Balas's *Disjunctive Programming*: the classical projection formula,
--   foundational to the whole chapter's projection track.
--
--   Let $Q := \{(u,x) : Au+Bx \le b\}$ and let $W := \{v : vA=0,\ v \ge 0\}$ be its projection
--   cone. Then
--
--   $$
--   \mathrm{Proj}_x(Q) = \{x \in \mathbb{R}^q : (vB)x \le vb,\ \forall v \in \mathrm{extr}(W)\}.
--   $$
--
--   That is, projecting out the $u$-variables amounts to premultiplying the system by every extreme
--   ray of the projection cone $W$ — a Fourier-Motzkin-style elimination stated once for an arbitrary
--   polyhedron $Q$, from which the chapter's later results (integrality, dimension, and facet
--   behavior under projection) all follow.
--
--   **Formalization Note.** `IsExtremeRay` requires the ray to be nonzero and its ray-set to be an
--   extreme subset of $W$ (Mathlib's `IsExtreme`), matching the classical notion of an extreme ray of
--   a pointed polyhedral cone.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 27, Theorem 2.5

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Theorem 2.5 (Balas §2.2, p. 27): the projection of `Q` onto the `x`-space is cut out by the
inequalities `(vB)x ≤ vb` for `v` ranging over the extreme rays of the projection cone `W`. -/
theorem projection_extreme_rays {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    ProjOntoX (Poly2 A B b) =
      {x : Fin q → ℝ | ∀ v, IsExtremeRay (ProjectionCone A) v →
        dotProduct (Matrix.vecMul v B) x ≤ dotProduct v b} := by sorry

end Disjunctive.Polarity
