-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_X
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_mul_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:45.899946+00:00
-- url     : https://prove2.me/theorems/e32111aa-cc45-47a0-a70b-9ba58bcb22ec
-- title:
--   Dwork Power Series Weights: jet Pair mul X
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L114-L122

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

theorem Formalism.DworkPowerSeriesWeights.jetPair_mul_X (P : MvPolynomial ι K) (i : ι) (F : MvPowerSeries ι K) :
    jetPair (P * MvPolynomial.X i) F = jetPair P (MvPowerSeries.pderiv K i F) := by sorry
