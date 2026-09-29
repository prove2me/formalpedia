-- Prove2me | Theorems.Thm_FamousTheorems_caratheodory_convexity
-- name    : FamousTheorems.caratheodory_convexity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:38.131177+00:00
-- url     : https://prove2.me/theorems/cb0e458f-ad42-4723-98b9-8ef6fb828cd5
-- title:
--   Carathéodory's convexity theorem
-- statement:
--   **Carathéodory's convexity theorem.** Let $s$ be a subset of a vector space $E$ over a linearly ordered field $\Bbbk$. Then the convex hull of $s$ is the union of the convex hulls of the finite affinely independent subsets of $s$:
--   $$\operatorname{conv}(s)=\bigcup_{\substack{t\subseteq s\text{ finite}\\ t\text{ affinely independent}}}\operatorname{conv}(t).$$
--
--   In $\mathbb R^d$ an affinely independent set has at most $d+1$ points. So every point of the convex hull of $s$ is a convex combination of at most $d+1$ points of $s$, which is the classical statement. The theorem is a basic result of convex geometry, used for example to show that the convex hull of a compact set in $\mathbb R^d$ is compact, and it is a companion of the Radon and Helly theorems.
--
--   **Formalization note.** Mathlib's `convexHull_eq_union`. The union runs over finsets `t` with `↑t ⊆ s` whose inclusion map `t → E` is `AffineIndependent`. The dimension bound $|t|\le d+1$ is not written into the statement. It follows from affine independence in finite dimension.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `convexHull_eq_union`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem caratheodory_convexity {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (s : Set E) :
    convexHull 𝕜 s =
      ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by sorry

end FamousTheorems
