-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BrC_phNorm_iff
-- name    : Formalism.L2.Th1.D.BrC.phNorm_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:39:15.92317+00:00
-- url     : https://prove2.me/theorems/c025f363-4f7a-4492-84e9-4db8454b7d79
-- title:
--   Br C: ph Norm iff
-- statement:
--   The Br C construction uses the ph Norm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SecondLevelOfNormHolds.lean#L214-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SecondLevelOfNormHolds.lean#L214-L218

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

theorem Formalism.L2.Th1.D.BrC.phNorm_iff {l : ℕ} {σ : K →+* K} (ph : PowerSeries K) (α : K) :
    C.PhNormAt (Formalism.G.unitBall K) (lgF K l) (expF K l) ph α (σ α) ↔ NormRel l σ ph α := by sorry
