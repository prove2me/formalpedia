-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BrC_all
-- name    : Formalism.L2.Th1.D.BrC.all
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:40.919021+00:00
-- url     : https://prove2.me/theorems/f0794499-fe1c-43df-b754-85444312538b
-- title:
--   Br C: all
-- statement:
--   The Br C construction uses the all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SecondLevelOfNormHolds.lean#L238-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SecondLevelOfNormHolds.lean#L238-L284

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.D.BrC
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable [CharZero K]

theorem Formalism.L2.Th1.D.BrC.all {l : ℕ} {σ : K →+* K} (hU : UnrOK K l σ) {F : MvPowerSeries (Fin 2) K}
    (hF : IsLawOfLog l F) {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0)
    (hF1 : F1 F (cob F ph))
    (hN : ∀ α : K, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ ph α) :
    C.Frame (Formalism.G.unitBall K) (lgF K l) (expF K l) ph ∧
    C.F1 (Formalism.G.unitBall K) (lgF K l) (expF K l) ph ∧
    F = C.fadd (lgF K l) (expF K l) (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∧
    ∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α →
      C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) ∧
      C.AdjAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) := by sorry
