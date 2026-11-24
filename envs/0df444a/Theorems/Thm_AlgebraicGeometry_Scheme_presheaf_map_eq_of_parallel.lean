-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
-- name    : AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:41.481593+00:00
-- url     : https://prove2.me/theorems/33084a4b-3064-4097-831d-c0fed66554fa
-- title:
--   Scheme: presheaf map eq of parallel
-- statement:
--   The Scheme construction uses the presheaf map eq of parallel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L175-L177

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.presheaf_map_eq_of_parallel (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ := by sorry
