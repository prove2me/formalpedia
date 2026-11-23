-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_linForm
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_mul_linForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:31.042038+00:00
-- url     : https://prove2.me/theorems/61e05942-10cd-4498-ba8f-ad99eff43f94
-- title:
--   Dwork Power Series Weights: jet Pair mul lin Form
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair mul lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L29-L36

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
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
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.jetPair_mul_linForm (P : MvPolynomial ι K) (L : ι → K) (F : MvPowerSeries ι K) :
    jetPair (P * linForm L) F = jetPair P (dirD L F) := by sorry
