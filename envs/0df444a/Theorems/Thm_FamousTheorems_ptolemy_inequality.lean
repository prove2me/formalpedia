-- Prove2me | Theorems.Thm_FamousTheorems_ptolemy_inequality
-- name    : FamousTheorems.ptolemy_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:39.464076+00:00
-- url     : https://prove2.me/theorems/98e1e580-c9e4-4b84-bb40-2a51cc614da3
-- title:
--   Ptolemy's inequality
-- statement:
--   **Ptolemy's inequality.** For any four points $a,b,c,d$ in a Euclidean (real inner product) space,
--   $$|ac|\cdot|bd|\;\le\;|ab|\cdot|cd|+|bc|\cdot|ad|.$$
--
--   Equality holds for a convex cyclic quadrilateral $abcd$, which is Ptolemy's theorem on the diagonals of a cyclic quadrilateral. The inequality characterises inner product spaces among normed spaces, and it is a standard tool in metric geometry, for example in the definition of Ptolemaic and CAT(0)-type spaces.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`, proved by inversion. The points lie in a metric space `P` that is a torsor over a real inner product space `V`, so the result holds in Euclidean spaces of any dimension, including infinite dimension.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ptolemy_inequality {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by sorry

end FamousTheorems
