-- Prove2me | Theorems.Thm_FamousTheorems_right_adjoints_preserve_limits_7a
-- name    : FamousTheorems.right_adjoints_preserve_limits_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:15.346197+00:00
-- url     : https://prove2.me/theorems/495c2830-c0d9-4a9d-ae21-baaf5433a254
-- title:
--   Right adjoints preserve limits (RAPL)
-- statement:
--   **Right adjoints preserve limits.** Let $F:C\to D$ be left adjoint to $G:D\to C$. Then $G$ preserves all limits that exist in $D$, of every size.
--
--   This principle is often abbreviated RAPL. It follows from the natural bijection $\operatorname{Hom}(Fc,d)\cong\operatorname{Hom}(c,Gd)$ and the universal property of limits. It explains many familiar facts: forgetful functors from groups, rings or modules to sets preserve products and kernels, and $\operatorname{Hom}(A,-)$ preserves limits. Dually, left adjoints preserve colimits, and tensor products distribute over direct sums.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`. `PreservesLimitsOfSize.{w, w'} G` says that $G$ preserves limits of all diagrams indexed by categories in universes $w,w'$, for arbitrary $w,w'$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w w'

theorem right_adjoints_preserve_limits_7a {C D : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D] {F : CategoryTheory.Functor C D}
    {G : CategoryTheory.Functor D C} (adj : CategoryTheory.Adjunction F G) :
    CategoryTheory.Limits.PreservesLimitsOfSize.{w, w'} G := by sorry

end FamousTheorems
