-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_ph_fadd
-- name    : Formalism.L2.Th1.C.FormalGroupJetIntegrality.ph_fadd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:32.758551+00:00
-- url     : https://prove2.me/theorems/3b40fd9c-25f3-5770-91b6-e7c803b63d8c
-- title:
--   Formal Group Jet Integrality: ph fadd
-- statement:
--   The Formal Group Jet Integrality construction uses the ph fadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L77-L83

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.FormalGroupJetIntegrality
open JetSubstitutionLemmas
variable {K : Type} [Field K] [CharZero K] {R : Subring K}

theorem Formalism.L2.Th1.C.FormalGroupJetIntegrality.ph_fadd {σ : Type} {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {a b : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (fadd l linv a b) ph =
      PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l)
        (PowerSeries.subst linv ph) := by sorry
