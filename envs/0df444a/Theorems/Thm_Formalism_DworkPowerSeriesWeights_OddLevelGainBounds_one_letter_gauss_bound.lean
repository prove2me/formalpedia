-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_one_letter_gauss_bound
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_gauss_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:47.325148+00:00
-- url     : https://prove2.me/theorems/e122e619-c26d-4c34-bf4b-c0387d78d491
-- title:
--   Odd Level Gain Bounds: one letter gauss bound
-- statement:
--   The Odd Level Gain Bounds construction uses the one letter gauss bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L87-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L87-L147

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
open OneGauss

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_gauss_bound : OneLetterGauss7 := by sorry
