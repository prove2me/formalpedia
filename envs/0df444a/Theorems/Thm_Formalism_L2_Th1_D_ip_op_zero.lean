-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_ip_op_zero
-- name    : Formalism.L2.Th1.D.ip_op_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:01.726359+00:00
-- url     : https://prove2.me/theorems/efdeb3ba-6226-4509-99e3-4beaa3347478
-- title:
--   D: ip op zero
-- statement:
--   The D construction uses the ip op zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L57-L63

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

theorem Formalism.L2.Th1.D.ip_op_zero (l : ℕ) (σ : K →+* K) :
    MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (0 : MvPowerSeries τ K)) = 0 := by sorry
