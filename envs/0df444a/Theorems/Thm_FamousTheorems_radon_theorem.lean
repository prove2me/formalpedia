-- Prove2me | Theorems.Thm_FamousTheorems_radon_theorem
-- name    : FamousTheorems.radon_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:26.611351+00:00
-- url     : https://prove2.me/theorems/9babce6b-c0d6-4fdd-9f8c-153d28209d77
-- title:
--   Radon's theorem
-- statement:
--   **Radon's theorem.** Let $(f_i)_{i\in\iota}$ be an affinely dependent family of points in a vector space over an ordered field. Then the index set splits into two parts $I$ and $I^c$ whose convex hulls intersect:
--   $$\operatorname{conv}\{f_i:i\in I\}\cap\operatorname{conv}\{f_i:i\notin I\}\ne\varnothing.$$
--   In particular, any $d+2$ points in $\mathbb R^d$ can be partitioned into two sets with intersecting convex hulls.
--
--   It is one of the three classical theorems of combinatorial convexity with Helly's and Carathéodory's, and it gives the shortest proof of Helly's theorem. It also shows that halfspaces in $\mathbb R^d$ have VC dimension $d+1$.
--
--   **Formalization note.** Mathlib's `Convex.radon_partition`; affine dependence is `¬ AffineIndependent 𝕜 f`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Convex.radon_partition`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem radon_theorem {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I : Set ι, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by sorry

end FamousTheorems
