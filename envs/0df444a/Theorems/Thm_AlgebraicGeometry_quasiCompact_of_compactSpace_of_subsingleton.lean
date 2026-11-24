-- Prove2me | Theorems.Thm_AlgebraicGeometry_quasiCompact_of_compactSpace_of_subsingleton
-- name    : AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:26.881799+00:00
-- url     : https://prove2.me/theorems/bf86cbe7-465c-4df1-b99c-841331338b46
-- title:
--   Algebraic Geometry: quasi Compact of compact Space of subsingleton
-- statement:
--   The Algebraic Geometry construction uses the quasi Compact of compact Space of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L200-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L200-L214

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

theorem AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton {W S : Scheme.{u}} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by sorry
