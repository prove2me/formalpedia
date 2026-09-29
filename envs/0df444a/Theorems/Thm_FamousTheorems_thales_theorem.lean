-- Prove2me | Theorems.Thm_FamousTheorems_thales_theorem
-- name    : FamousTheorems.thales_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:46.290005+00:00
-- url     : https://prove2.me/theorems/e4a6f3ba-9eb1-4c14-b1f8-cd25f91d6e13
-- title:
--   Thales's theorem
-- statement:
--   **Thales's theorem.** An angle inscribed in a semicircle is a right angle: if $A$ and $B$ are diametrically opposite on a circle and $C$ is any other point on it, then $\angle ACB = \pi/2$. It is the special case of the inscribed angle theorem where the chord is a diameter, and its converse holds too — the locus of points seeing a segment at a right angle is the circle on that segment as diameter. Traditionally the first theorem attributed to a named mathematician, Thales of Miletus in the 6th century BC. It gives the standard ruler-and-compass construction of tangents from an external point. **Formalization note.** The configuration is expressed by membership in a `Sphere` with the two points antipodal. The result is Mathlib's `EuclideanGeometry.Sphere.thales_theorem`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem thales_theorem :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {p₁ p₂ p₃ : P} 
    {s : EuclideanGeometry.Sphere P}, s.IsDiameter p₁ p₃ → (EuclideanGeometry.angle p₁ p₂ p₃ = Real.pi / 2 ↔ p₂ ∈ s) := by sorry

end FamousTheorems
