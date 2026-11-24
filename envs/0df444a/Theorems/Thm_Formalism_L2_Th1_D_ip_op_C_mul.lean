-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_ip_op_C_mul
-- name    : Formalism.L2.Th1.D.ip_op_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:06.3288+00:00
-- url     : https://prove2.me/theorems/96555f2c-4055-4629-8eb9-da0a754e0a0e
-- title:
--   D: ip op C mul
-- statement:
--   The D construction uses the ip op C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L75-L85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand

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
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
variable {K : Type} [NormedField K] {τ : Type}

theorem Formalism.L2.Th1.D.ip_op_C_mul (l : ℕ) (σ : K →+* K) (c : K) (g : MvPowerSeries τ K) :
    MvPowerSeries.C ((l : K)⁻¹) *
        frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (MvPowerSeries.C c * g)) =
      MvPowerSeries.C (σ (σ c)) *
        (MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g)) := by sorry
