-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_SubstitutionCoefficientLemmas_subst_scale
-- name    : Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.subst_scale
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:06.217493+00:00
-- url     : https://prove2.me/theorems/e85f82fe-f8fa-4e03-ac6f-7b39d0007fc6
-- title:
--   Substitution Coefficient Lemmas: subst scale
-- statement:
--   The Substitution Coefficient Lemmas construction uses the subst scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IntegralPartAtVariable.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IntegralPartAtVariable.lean#L42-L50

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IntegralPartAtVariable
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.SubstitutionCoefficientLemmas
open Pair InverseCommuting
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.subst_scale {τ : Type} {G H : MvPowerSeries τ K} (hG : constantCoeff G = 0)
    (hH : constantCoeff H = 0) (a b : K) (B : MvPowerSeries (Fin 2) K) :
    subst ![C a * G, C b * H] B = subst ![G, H] (rescale ![a, b] B) := by sorry
