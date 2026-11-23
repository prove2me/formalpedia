-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_C_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:26.206063+00:00
-- url     : https://prove2.me/theorems/147a89a4-8adf-4500-b5d0-b736358d8c74
-- title:
--   Dwork Power Series Weights: jet Pair C left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair C left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L75-L84

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_C_left (c : K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c) F = c * MvPowerSeries.constantCoeff F := by sorry
