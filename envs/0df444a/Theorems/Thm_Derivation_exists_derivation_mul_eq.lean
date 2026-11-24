-- Prove2me | Theorems.Thm_Derivation_exists_derivation_mul_eq
-- name    : Derivation.exists_derivation_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:50.865804+00:00
-- url     : https://prove2.me/theorems/26e3ce56-2896-4a6b-bd80-ee0696f11431
-- title:
--   Derivation: exists derivation mul eq
-- statement:
--   The Derivation construction uses the exists derivation mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DerivationLocalization.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DerivationLocalization.lean#L83-L94

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

theorem Derivation.exists_derivation_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D s = algebraMap S S' (D₀ s) := by sorry
