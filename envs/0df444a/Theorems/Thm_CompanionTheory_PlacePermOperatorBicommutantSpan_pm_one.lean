-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_pm_one
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.pm_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:59.548177+00:00
-- url     : https://prove2.me/theorems/e4783ed8-c84e-4858-8f7d-0b833e130db2
-- title:
--   Place Perm Operator Bicommutant Span: pm one
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the pm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L49-L53

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.pm_one : pm (1 : K) 0 (0 : Fin M → K) 1 0 1 = 1 := by sorry
