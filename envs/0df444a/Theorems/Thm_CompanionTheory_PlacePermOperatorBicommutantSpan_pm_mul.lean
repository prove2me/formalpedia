-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_pm_mul
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.pm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:50.918809+00:00
-- url     : https://prove2.me/theorems/58377abc-c742-4b36-bb7a-e47fc59aa9f1
-- title:
--   Place Perm Operator Bicommutant Span: pm mul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the pm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L44-L47

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.pm_mul (a b d a' b' d' : K) (r w r' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    pm a b r d w U * pm a' b' r' d' w' U' =
      pm (a * a') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + r ᵥ* U') (d * d') (d' • w + U *ᵥ w') (U * U') := by sorry
