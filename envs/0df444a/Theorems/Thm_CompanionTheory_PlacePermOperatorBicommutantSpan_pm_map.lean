-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_pm_map
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.pm_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:09.686312+00:00
-- url     : https://prove2.me/theorems/31b83f48-6cb5-41ca-a121-f99e2410fafb
-- title:
--   Place Perm Operator Bicommutant Span: pm map
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the pm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L61-L64

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.pm_map {L : Type} [CommRing L] (φ : K →+* L) (a b d : K) (r w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (pm a b r d w U).map φ = pm (φ a) (φ b) (φ ∘ r) (φ d) (φ ∘ w) (U.map φ) := by sorry
