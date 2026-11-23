-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:27.011311+00:00
-- url     : https://prove2.me/theorems/5cc8a9f1-1011-4d9f-9adc-58e3bb6bf92a
-- title:
--   Dwork Power Series Weights: jet Pair C mul left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair C mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L41-L51

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c * P) F = c * jetPair P F := by sorry
