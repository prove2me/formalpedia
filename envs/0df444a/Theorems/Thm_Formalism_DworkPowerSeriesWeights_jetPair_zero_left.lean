-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_zero_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:14.817874+00:00
-- url     : https://prove2.me/theorems/6c3678c2-bb6d-4dff-9371-065e40d8e237
-- title:
--   Dwork Power Series Weights: jet Pair zero left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L38-L39

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}

theorem Formalism.DworkPowerSeriesWeights.jetPair_zero_left (F : MvPowerSeries ι K) : jetPair (0 : MvPolynomial ι K) F = 0 := by sorry
