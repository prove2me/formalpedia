-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_third
-- name    : Formalism.L2.Th1.C.FormalGroupJetIntegrality.third
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:27.012832+00:00
-- url     : https://prove2.me/theorems/31c85329-79fd-5475-ab0d-3c96bde65871
-- title:
--   Formal Group Jet Integrality: third
-- statement:
--   The Formal Group Jet Integrality construction uses the third property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L85-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L85-L140

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

theorem Formalism.L2.Th1.C.FormalGroupJetIntegrality.third {l linv ph : PowerSeries K} (hFr : Frame R l linv ph) (hF1 : F1 R l linv ph) :
    IntMv R (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) l +
          PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) l)
        ((PowerSeries.derivative K)^[3] (PowerSeries.subst linv ph)) *
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l) *
      PowerSeries.subst (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K)
        (PowerSeries.derivative K l)) := by sorry
