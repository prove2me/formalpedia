-- Prove2me | Theorems.Thm_CompanionTheory_WaveGrid_LimSh_letters_pow_mono
-- name    : CompanionTheory.WaveGrid.LimSh.letters_pow_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:56.877741+00:00
-- url     : https://prove2.me/theorems/251d2158-78f5-44a0-907e-58778413ee5d
-- title:
--   Lim Sh: letters pow mono
-- statement:
--   The Lim Sh construction uses the letters pow mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/LettersPoly.lean#L22-L25

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

theorem CompanionTheory.WaveGrid.LimSh.letters_pow_mono {a d : ℕ} (h : a ≤ d) : Letters k r ^ a ≤ Letters k r ^ d := by sorry
