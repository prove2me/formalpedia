-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_logb_max_one_nat
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.logb_max_one_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:20.522877+00:00
-- url     : https://prove2.me/theorems/6a0cfd3b-5463-4330-b578-a730fa531bea
-- title:
--   Odd Level Gain Bounds: logb max one nat
-- statement:
--   The Odd Level Gain Bounds construction uses the logb max one nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TheoremAMonomialOfLemmas.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/TheoremAMonomialOfLemmas.lean#L14-L18

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TheoremAMonomialOfLemmas
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.logb_max_one_nat (l n : ℕ) :
    Real.logb (l : ℝ) ((max 1 n : ℕ) : ℝ) = Real.logb (l : ℝ) (n : ℝ) := by sorry
