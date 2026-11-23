-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_eta
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.blk_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:13.887915+00:00
-- url     : https://prove2.me/theorems/1d9290e0-b739-4da1-9561-248abf956002
-- title:
--   Place Perm Operator Bicommutant Span: blk eta
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the blk eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L19-L24

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.blk_eta (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) :
    g = blk (g 0 0) (g 0 1) (fun j => g 0 j.succ.succ) (g 1 0) (g 1 1) (fun j => g 1 j.succ.succ)
      (fun i => g i.succ.succ 0) (fun i => g i.succ.succ 1) (Matrix.of fun i j => g i.succ.succ j.succ.succ) := by sorry
