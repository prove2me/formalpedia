-- Prove2me | Theorems.Thm_Derivation_liftToLocalization_algebraMap
-- name    : Derivation.liftToLocalization_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:22.196459+00:00
-- url     : https://prove2.me/theorems/d380d950-cefa-4988-94ce-b55ad4a4e95f
-- title:
--   Derivation: lift To Localization algebra Map
-- statement:
--   The Derivation construction uses the lift To Localization algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DerivationLocalization.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DerivationLocalization.lean#L60-L63

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w x
variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]
open Derivation

theorem Derivation.liftToLocalization_algebraMap (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.liftToLocalization (S' := S') M) (algebraMap S S' s) = D s := by sorry
