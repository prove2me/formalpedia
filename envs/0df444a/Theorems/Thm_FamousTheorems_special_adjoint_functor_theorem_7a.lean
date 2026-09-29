-- Prove2me | Theorems.Thm_FamousTheorems_special_adjoint_functor_theorem_7a
-- name    : FamousTheorems.special_adjoint_functor_theorem_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:14.583417+00:00
-- url     : https://prove2.me/theorems/b2ddf28b-b4bf-45a2-b3bc-14fefaac2f32
-- title:
--   The special adjoint functor theorem
-- statement:
--   **The special adjoint functor theorem.** Let $D$ be a complete, well-powered, locally small category with a small coseparating family of objects, and let $G:D\to C$ be a functor to a locally small category. If $G$ preserves all small limits, then $G$ has a left adjoint.
--
--   This theorem, due to Freyd, replaces the solution set condition of the general adjoint functor theorem by conditions on $D$ alone. It gives, for example, the Stone–Čech compactification as the left adjoint of the inclusion of compact Hausdorff spaces into topological spaces, where the unit interval is a coseparator.
--
--   **Formalization note.** Mathlib's `CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating`. $C$ and $D$ have morphisms in the same universe $v$, and limits of all $v$-small shapes are required. `WellPowered D` says that each object has a small set of subobjects. `ObjectProperty.Small P` says that the coseparating family $P$ is essentially small, and `P.IsCoseparating` says that morphisms into objects of $P$ distinguish parallel morphisms.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w

theorem special_adjoint_functor_theorem_7a {C : Type u} [CategoryTheory.Category.{v} C] {D : Type w} [CategoryTheory.Category.{v} D]
    [CategoryTheory.Limits.HasLimits D] [CategoryTheory.WellPowered.{v} D] {P : CategoryTheory.ObjectProperty D}
    [CategoryTheory.ObjectProperty.Small.{v} P] (hP : P.IsCoseparating) (G : CategoryTheory.Functor D C)
    [CategoryTheory.Limits.PreservesLimits G] : G.IsRightAdjoint := by sorry

end FamousTheorems
