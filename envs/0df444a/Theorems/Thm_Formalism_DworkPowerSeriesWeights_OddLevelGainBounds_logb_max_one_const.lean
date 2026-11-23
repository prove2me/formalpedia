-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_logb_max_one_const
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.logb_max_one_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:22.8653+00:00
-- url     : https://prove2.me/theorems/fb0f7972-21c7-4f64-a826-8d3b60be0a6b
-- title:
--   Odd Level Gain Bounds: logb max one const
-- statement:
--   The Odd Level Gain Bounds construction uses the logb max one const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L79-L84

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.logb_max_one_const (l C : ℕ) :
    Real.logb l ((max 1 C : ℕ) : ℝ) = Real.logb l (C : ℝ) := by sorry
