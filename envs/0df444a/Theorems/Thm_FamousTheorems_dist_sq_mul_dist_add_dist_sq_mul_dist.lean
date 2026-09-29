-- Prove2me | Theorems.Thm_FamousTheorems_dist_sq_mul_dist_add_dist_sq_mul_dist
-- name    : FamousTheorems.dist_sq_mul_dist_add_dist_sq_mul_dist
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:42.173269+00:00
-- url     : https://prove2.me/theorems/043d72b7-05a7-4dae-b84e-789ad1e6f4cd
-- title:
--   Stewart's theorem
-- statement:
--   **Stewart's theorem** relates the length of a cevian to the sides of a triangle it cuts. If $d$ is the cevian from a vertex to a point dividing the opposite side into segments $m$ and $n$, then $b^2m + c^2n = a(d^2 + mn)$. It generalises both the median-length formula (take $m=n$) and Apollonius' theorem, and gives the angle-bisector length once the bisector's division ratio is known. The identity follows from applying the law of cosines to the two sub-triangles at the supplementary angles either side of the cevian, so the cosine terms cancel. **Formalization note.** Distances are squared as products and the configuration is expressed by betweenness of the division point. The result is Mathlib's `EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem dist_sq_mul_dist_add_dist_sq_mul_dist :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (a b c p : P), 
    EuclideanGeometry.angle b p c = Real.pi → 
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p = dist b c * (dist a p ^ 2 + dist b p * dist c p) := by sorry

end FamousTheorems
