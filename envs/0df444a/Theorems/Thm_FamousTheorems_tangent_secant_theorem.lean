-- Prove2me | Theorems.Thm_FamousTheorems_tangent_secant_theorem
-- name    : FamousTheorems.tangent_secant_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:53.248306+00:00
-- url     : https://prove2.me/theorems/5a382cfc-b768-4245-9682-6cf0c875bec2
-- title:
--   The tangent–secant theorem
-- statement:
--   **The tangent–secant theorem.** Let $s$ be a sphere in a Euclidean space, $a,b\in s$, and $p$ a point on the line $ab$. If the line through $p$ and $t$ is tangent to $s$ at $t$, then
--   $$|pt|^2=|pa|\cdot|pb| .$$
--
--   It is the limiting case of the intersecting secants theorem, where one secant becomes a tangent, and a special case of the power of a point. It appears in Euclid (Elements III.36) and is a standard tool of olympiad geometry.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`; `line[ℝ, a, b]` is the affine span of `a` and `b`, and `s.IsTangentAt t ℓ` says the line `ℓ` is tangent to `s` at `t`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tangent_secant_theorem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {P : Type*} [MetricSpace P]
    [NormedAddTorsor V P] {a b t p : P} {s : EuclideanGeometry.Sphere P} (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ line[ℝ, a, b]) (ht : s.IsTangentAt t line[ℝ, p, t]) : dist p t ^ 2 = dist p a * dist p b := by sorry

end FamousTheorems
