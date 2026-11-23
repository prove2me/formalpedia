-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_two_gamma_le_three_div
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.two_gamma_le_three_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:30.533917+00:00
-- url     : https://prove2.me/theorems/9d70a236-e886-4468-b849-69aecde364b8
-- title:
--   Odd Level Gain Bounds: two gamma le three div
-- statement:
--   The Odd Level Gain Bounds construction uses the two gamma le three div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L28-L36

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.two_gamma_le_three_div {l : ℕ} (hl : 3 ≤ l) : 2 * gam l ≤ 3 / (l : ℝ) := by sorry
