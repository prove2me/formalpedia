-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gain_dominates_oddLevel_sum
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_dominates_oddLevel_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:23.749285+00:00
-- url     : https://prove2.me/theorems/89225400-5198-46ff-8dcd-02945cf66e86
-- title:
--   Odd Level Gain Bounds: gain dominates odd Level sum
-- statement:
--   The Odd Level Gain Bounds construction uses the gain dominates odd Level sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/GainDominatesOddLevelSum.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/GainDominatesOddLevelSum.lean#L13-L13

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_TheoremATwoFormsOfEntry
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_GainDominatesOddLevelSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.gain_dominates_oddLevel_sum : GainDominatesInnerSum := by sorry
