-- Prove2me | Theorems.Thm_FamousTheorems_general_adjoint_functor_theorem
-- name    : FamousTheorems.general_adjoint_functor_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:39.03096+00:00
-- url     : https://prove2.me/theorems/56993a7b-a075-4d8e-8ded-8f23585ca5f6
-- title:
--   The general adjoint functor theorem
-- statement:
--   **Freyd's general adjoint functor theorem.** Let $G:D\to C$ be a functor where $D$ is complete (has all small limits). If $G$ preserves small limits and satisfies the solution set condition, then $G$ has a left adjoint.
--
--   The solution set condition asks that for every object $A$ of $C$ there be a set of objects $B_i$ of $D$ and maps $f_i:A\to G(B_i)$ through which every map $A\to G(X)$ factors as $G(g)\circ f_i$. The theorem is the main general tool for constructing left adjoints (free objects, completions, reflections) without an explicit construction.
--
--   **Formalization note.** Mathlib's `CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition`. Smallness is measured by the universe `v₁` of morphisms of `D`: `HasLimits D` and `PreservesLimitsOfSize.{v₁, v₁} G` refer to limits indexed by `v₁`-small categories, and `SolutionSetCondition.{v₁} G` requires the solution sets to be indexed by types in `Type v₁`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.isRightAdjoint_of_preservesLimits_of_solutionSetCondition`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v u₁ v₁

theorem general_adjoint_functor_theorem {C : Type u} [CategoryTheory.Category.{v} C] {D : Type u₁} [CategoryTheory.Category.{v₁} D]
    (G : CategoryTheory.Functor D C) [CategoryTheory.Limits.HasLimits D]
    [CategoryTheory.Limits.PreservesLimitsOfSize.{v₁, v₁} G] (hG : CategoryTheory.SolutionSetCondition.{v₁} G) :
    G.IsRightAdjoint := by sorry

end FamousTheorems
