-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hform_eq
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.hform_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:42.114798+00:00
-- url     : https://prove2.me/theorems/8dceb5a7-b7b8-473f-a0a7-5f688519368e
-- title:
--   Place Perm Operator Bicommutant Span: hform eq
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L79-L82

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.hform_eq (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J x y = ((s ∘ x) ᵥ* J) ⬝ᵥ y := by sorry
