-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_ip_expand_congr
-- name    : Formalism.L2.Th1.D.ip_expand_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:46.429911+00:00
-- url     : https://prove2.me/theorems/57528704-1886-4100-b757-ef6d1a567b3b
-- title:
--   D: ip expand congr
-- statement:
--   The D construction uses the ip expand congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L116-L119

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

theorem Formalism.L2.Th1.D.ip_expand_congr {K τ : Type} [Field K] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b)
    (f : MvPowerSeries τ K) : MvPowerSeries.expand a ha f = MvPowerSeries.expand b hb f := by sorry
