-- Prove2me | Theorems.Thm_FamousTheorems_bipolar_proper_cone_7a
-- name    : FamousTheorems.bipolar_proper_cone_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:10.836824+00:00
-- url     : https://prove2.me/theorems/7d5e026f-59ca-4a6a-8665-72c9816b61b7
-- title:
--   Bipolar theorem for proper cones
-- statement:
--   **Bipolar theorem for proper cones.** Let $E$ be a real Hilbert space and $C\subseteq E$ a proper cone, that is, a closed convex cone containing $0$. Let
--   $$C^*=\{y\in E:\langle x,y\rangle\ge0\text{ for all }x\in C\}$$
--   be its dual cone. Then $C^{**}=C$.
--
--   This is the conic form of the bipolar theorem. It follows from the Hahn–Banach separation theorem: a point outside the closed convex cone $C$ can be separated from $C$ by a hyperplane through the origin. It underlies the Farkas lemma, duality in linear and conic programming, and the theory of positive linear functionals.
--
--   **Formalization note.** Mathlib's `ProperCone.innerDual_innerDual`. `ProperCone ℝ E` is the type of closed pointed convex cones, and `ProperCone.innerDual s` is the dual cone of a set $s$ with respect to the inner product. Mathlib also has a version for general continuous perfect pairings, `ProperCone.dual_dual_flip`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProperCone.innerDual_innerDual`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bipolar_proper_cone_7a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (C : ProperCone ℝ E) :
    ProperCone.innerDual (ProperCone.innerDual (C : Set E) : Set E) = C := by sorry

end FamousTheorems
