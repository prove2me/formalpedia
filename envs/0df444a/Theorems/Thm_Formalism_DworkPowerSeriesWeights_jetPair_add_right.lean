-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_add_right
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:33.39853+00:00
-- url     : https://prove2.me/theorems/1bb229cc-73f7-41f1-946d-1dfbae653568
-- title:
--   Dwork Power Series Weights: jet Pair add right
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L60-L62

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_add_right (P : MvPolynomial ι K) (F G : MvPowerSeries ι K) :
    jetPair P (F + G) = jetPair P F + jetPair P G := by sorry
