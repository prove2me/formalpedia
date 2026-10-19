-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_component_separate_properties
-- name    : EnsembleSpaceDraft.component_separate_properties
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:49:55.181508+00:00
-- url     : https://prove2.me/theorems/2e968ee2-ba91-4ecb-b474-cd187f89a223
-- title:
--   Corollary 1.25 — components and separateness
-- statement:
--   In any ensemble space the following hold.
--
--   1. Every ensemble is a component of itself.
--   2. If $a$ is a component of $b$, then $a$ and $b$ have a common component, and therefore they are not separate.
--   3. Separateness is irreflexive and symmetric: no ensemble is separate from itself, and $a$ is separate from $b$ if and only if $b$ is separate from $a$.
--   4. Distinct extreme points are separate.
--   5. An internal point has a common component with every ensemble, and therefore is not separate from any ensemble.
--   6. If two ensembles are separate, then both are boundary points.
--
--   Components, separateness, extreme points, internal points, and boundary points are those of Definitions 1.19, 1.20 and 1.24. This is Corollary 1.25.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Corollary 1.25, pp. 22–23.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

/-- Corollary 1.25. Basic properties of components and separateness. -/
theorem component_separate_properties {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E) :
    (∀ e : E, X.IsComponent e e) ∧
      (∀ a b : E, X.IsComponent a b → X.HasCommonComponent a b ∧ ¬ X.Separate a b) ∧
      (∀ a : E, ¬ X.Separate a a) ∧
      (∀ a b : E, X.Separate a b ↔ X.Separate b a) ∧
      (∀ a b : E, X.IsExtreme a → X.IsExtreme b → a ≠ b → X.Separate a b) ∧
      (∀ e a : E, X.IsInternal e → X.HasCommonComponent e a ∧ ¬ X.Separate e a) ∧
      (∀ a b : E, X.Separate a b → X.IsBoundary a ∧ X.IsBoundary b) := by
  sorry

end EnsembleSpaceDraft
