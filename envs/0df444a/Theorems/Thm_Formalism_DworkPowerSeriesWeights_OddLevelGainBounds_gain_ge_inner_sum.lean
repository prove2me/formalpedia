-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gain_ge_inner_sum
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_ge_inner_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:59.702751+00:00
-- url     : https://prove2.me/theorems/c1c6a790-08ca-475e-872f-4fb67a23753e
-- title:
--   Odd Level Gain Bounds: gain ge inner sum
-- statement:
--   The Odd Level Gain Bounds construction uses the gain ge inner sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L194-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/CompanionTheory.lean#L194-L248

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

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_ge_inner_sum : GainDominatesInnerSum := by sorry
