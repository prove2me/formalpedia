-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_sum_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:46.270721+00:00
-- url     : https://prove2.me/theorems/822e7e3d-b8ea-401a-9c49-fe3d075bf3f1
-- title:
--   Dwork Power Series Weights: jet Pair sum left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L53-L58

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_sum_left {α : Type*} (s : Finset α) (P : α → MvPolynomial ι K)
    (F : MvPowerSeries ι K) : jetPair (∑ a ∈ s, P a) F = ∑ a ∈ s, jetPair (P a) F := by sorry
