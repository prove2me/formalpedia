-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_subst_zero
-- name    : Formalism.L2.Th1.C.FormalGroupJetIntegrality.subst_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:32:45.366972+00:00
-- url     : https://prove2.me/theorems/9c7c777d-d4c6-4930-ab89-b98cf2a76736
-- title:
--   Formal Group Jet Integrality: subst zero
-- statement:
--   The Formal Group Jet Integrality construction uses the subst zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L17-L24

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
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.FormalGroupJetIntegrality.subst_zero {τ : Type} (g : PowerSeries K) :
    PowerSeries.subst (0 : MvPowerSeries τ K) g =
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by sorry
