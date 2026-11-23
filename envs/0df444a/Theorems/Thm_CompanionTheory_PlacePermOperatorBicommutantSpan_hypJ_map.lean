-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hypJ_map
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.hypJ_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:29.332096+00:00
-- url     : https://prove2.me/theorems/6eeac9ff-fd01-4c9e-bbb5-3628a8e01769
-- title:
--   Place Perm Operator Bicommutant Span: hyp J map
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the hyp J map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L74-L77

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.hypJ_map {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by sorry
