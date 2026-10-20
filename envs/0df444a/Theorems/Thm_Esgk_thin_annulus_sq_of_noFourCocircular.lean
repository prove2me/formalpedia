-- Prove2me | Theorems.Thm_Esgk_thin_annulus_sq_of_noFourCocircular
-- name    : Esgk.thin_annulus_sq_of_noFourCocircular
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-20T05:13:36.641811+00:00
-- url     : https://prove2.me/theorems/64fbcd66-435f-4d4e-b369-545bf872b0bb
-- title:
--   Few distinct distances force a thin annulus about the centroid
-- statement:
--   Let $n\ge 1$ and let $p=(p_1,\dots,p_n)$ be an injective configuration of $n$ points in the plane, with image $P=\{p_1,\dots,p_n\}$. Assume that no four points of $P$ lie on a common circle. Let $R$ be the set of distances $|x-y|$ with $x,y\in P$ and $x\ne y$, and let $D(P)=|R|$ be the number of distinct distances determined by $P$. Put
--
--   $$
--   c=\frac1n\sum_{j=1}^n p_j,\qquad M=\sum_{i=1}^n |p_i-c|^2,\qquad \rho^2=\frac1n\Bigl(3\sum_{r\in R} r^2-M\Bigr).
--   $$
--
--   If $\delta$ is a real number with $D(P)\le(1/3+\delta)\,n$, then every index $i$ satisfies
--
--   $$
--   \rho^2\Bigl(1-12\delta-\frac4n\Bigr)\le |p_i-c|^2\le \rho^2 .
--   $$
--
--   A circle about a point of $P$ contains at most three other points of $P$, so $3D(P)\ge n-1$. The theorem is a stability statement for this bound: when $D(P)$ is at most $(1/3+\delta)n$, all points lie in an annulus about the centroid of relative squared width $12\delta+4/n$. No hypothesis on collinear points is used.
--
--   **Formalization Note** Here $c$ is `configCentroid p`, $M$ is `centroidSquaredMass p`, $\rho^2$ is `distanceAnnulusRadiusSq p`, and $R$ is `OrderedDistanceValues p`, the set of values $|p_i-p_j|$ with $i\ne j$, which is the distance set of $P$ because $p$ is injective. $D(P)$ is `NumDistances p`. "On a common circle" is Mathlib's `Cospherical` in the Euclidean plane, applied to four-element subsets of $P$.
-- source:
--   Lean formalization by Adam McKenna (2026), declaration Esgk.thin_annulus_sq_of_noFourCocircular.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_ConfigurationCentroid
import Definitions.Def_Esgk_ThinAnnulus

open EuclideanGeometry Esgk

namespace Esgk

theorem thin_annulus_sq_of_noFourCocircular {n : ℕ} {p : Config n}
    (hp : Function.Injective p)
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 0 < n) {δ : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ)) :
    ∀ i, distanceAnnulusRadiusSq p * (1 - 12 * δ - 4 / (n : ℝ)) ≤
        dist (p i) (configCentroid p) ^ 2 ∧
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by sorry

end Esgk
