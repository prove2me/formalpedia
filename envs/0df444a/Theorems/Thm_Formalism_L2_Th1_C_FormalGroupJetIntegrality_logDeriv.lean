-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_logDeriv
-- name    : Formalism.L2.Th1.C.FormalGroupJetIntegrality.logDeriv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:55.360078+00:00
-- url     : https://prove2.me/theorems/25eb9734-6c14-4127-9c35-a471f691bef2
-- title:
--   Formal Group Jet Integrality: log Deriv
-- statement:
--   The Formal Group Jet Integrality construction uses the log Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L26-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntegralThirdInvariantDerivative.lean#L26-L69

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
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

theorem Formalism.L2.Th1.C.FormalGroupJetIntegrality.logDeriv {R : Subring K} {l linv : PowerSeries K} (h : IsLogPair l linv)
    (hF : FGInt R l linv) : IsOneUnit R (PowerSeries.derivative K l) := by sorry
