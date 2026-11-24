-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_SubstitutionCoefficientLemmas_right_eq
-- name    : Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.right_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:24.429568+00:00
-- url     : https://prove2.me/theorems/55bc4b20-6519-4507-8cdd-2e6ab2b701c7
-- title:
--   Substitution Coefficient Lemmas: right eq
-- statement:
--   The Substitution Coefficient Lemmas construction uses the right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IntegralPartAtVariable.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IntegralPartAtVariable.lean#L68-L77

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

theorem Formalism.L2.Th1.D.SubstitutionCoefficientLemmas.right_eq {l : ℕ} (hl : 2 ≤ l) {β : K} {e : PowerSeries K} (he : IsMul l β e)
    (be0 : MvPowerSeries (Fin 2) K) :
    subst ![at1 (0 : Fin 2) (lgF K l), C β * at1 (1 : Fin 2) (lgF K l)] (addC l be0) =
      subst ![X 0, at1 (1 : Fin 2) e] be0 := by sorry
