-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_qw_eq_prod
-- name    : CompanionTheory.WaveGrid.qw_eq_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:32.877813+00:00
-- url     : https://prove2.me/theorems/af7c6874-9412-469e-8cb9-a87a8abe4094
-- title:
--   Wave Grid: qw eq prod
-- statement:
--   The Wave Grid construction uses the qw eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean#L13-L23

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt

theorem CompanionTheory.WaveGrid.qw_eq_prod {S : Type} [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (L : List (Wd.Letter ℂ S)) (Y : ℂ) :
    Wd.qw q L Y = q Y * (L.map fun l => facW l Y).prod := by sorry
