-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_intMv_sum
-- name    : Formalism.L2.Th1.E.CompatibleChartOperations.intMv_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:25.232857+00:00
-- url     : https://prove2.me/theorems/71f26c25-0737-40dd-bc52-4cf3a160d6d5
-- title:
--   Compatible Chart Operations: int Mv sum
-- statement:
--   The Compatible Chart Operations construction uses the int Mv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInVarEqZero.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ConstantCoeffInVarEqZero.lean#L28-L32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)
open Formalism.L2.Th1.E.CompatibleChartOperations
variable {K : Type} [Field K] {σ : Type} {R : Subring K}

theorem Formalism.L2.Th1.E.CompatibleChartOperations.intMv_sum {κ : Type} (s : Finset κ) {F : κ → MvPowerSeries σ K}
    (hF : ∀ k ∈ s, IntMv R (F k)) : IntMv R (∑ k ∈ s, F k) := by sorry
