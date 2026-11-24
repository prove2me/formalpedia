-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_range_comp_base
-- name    : AlgebraicGeometry.Scheme.Hom.range_comp_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:21.265222+00:00
-- url     : https://prove2.me/theorems/a2ef1148-0757-4fd8-a54e-b648efd3419e
-- title:
--   Hom: range comp base
-- statement:
--   The Hom construction uses the range comp base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L187-L194

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
open AlgebraicGeometry.Scheme.Hom

theorem AlgebraicGeometry.Scheme.Hom.range_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by sorry
