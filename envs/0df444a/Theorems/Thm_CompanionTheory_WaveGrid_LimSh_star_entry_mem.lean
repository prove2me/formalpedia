-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_LimSh_star_entry_mem
-- name    : CompanionTheory.WaveGrid.LimSh.star_entry_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:00.748612+00:00
-- url     : https://prove2.me/theorems/75ea9b5f-63bd-51d1-be50-ab57b52c9d30
-- title:
--   Lim Sh: star entry mem
-- statement:
--   The Lim Sh construction uses the star entry mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L35-L49

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.LimSh
open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main
variable {k r : ℕ}

theorem CompanionTheory.WaveGrid.LimSh.star_entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => star (g i j)) ∈ Letters k r := by sorry
