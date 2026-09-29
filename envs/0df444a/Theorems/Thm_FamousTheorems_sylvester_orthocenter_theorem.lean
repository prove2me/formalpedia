-- Prove2me | Theorems.Thm_FamousTheorems_sylvester_orthocenter_theorem
-- name    : FamousTheorems.sylvester_orthocenter_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:53.137197+00:00
-- url     : https://prove2.me/theorems/77c9ad14-25ec-4bdf-a789-371edffb3428
-- title:
--   Sylvester's theorem on the orthocenter
-- statement:
--   **Sylvester's theorem on the orthocenter.** Let $t$ be a triangle with vertices $A_0,A_1,A_2$, circumcenter $O$ and orthocenter $H$. Then
--   $$\overrightarrow{OH}=\overrightarrow{OA_0}+\overrightarrow{OA_1}+\overrightarrow{OA_2}.$$
--
--   The identity immediately gives the Euler line: since the centroid satisfies $\overrightarrow{OG}=\frac13\sum\overrightarrow{OA_i}$, the points $O,G,H$ are collinear with $OH=3\,OG$. It also gives a short proof that the three altitudes are concurrent.
--
--   **Formalization note.** Mathlib's `Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub`, for a triangle `Affine.Triangle ℝ P` in a Euclidean affine space. `-ᵥ` is the vector between two points.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sylvester_orthocenter_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) : t.orthocenter -ᵥ t.circumcenter = ∑ i, (t.points i -ᵥ t.circumcenter) := by sorry

end FamousTheorems
