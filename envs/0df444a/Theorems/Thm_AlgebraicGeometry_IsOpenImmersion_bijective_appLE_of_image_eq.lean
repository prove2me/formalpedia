-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_bijective_appLE_of_image_eq
-- name    : AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:39.937937+00:00
-- url     : https://prove2.me/theorems/6d88da1a-e339-4ed5-a9d3-6ab25e4f4d43
-- title:
--   Is Open Immersion: bijective app LE of image eq
-- statement:
--   The Is Open Immersion construction uses the bijective app LE of image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/OpenImmersionAppLE.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/OpenImmersionAppLE.lean#L11-L32

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry
open CategoryTheory
universe u
open AlgebraicGeometry.IsOpenImmersion

theorem AlgebraicGeometry.IsOpenImmersion.bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by sorry
