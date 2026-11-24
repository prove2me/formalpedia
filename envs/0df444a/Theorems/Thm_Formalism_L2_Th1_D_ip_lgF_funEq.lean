-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_ip_lgF_funEq
-- name    : Formalism.L2.Th1.D.ip_lgF_funEq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:42.873503+00:00
-- url     : https://prove2.me/theorems/60bd7057-9bc0-45cf-8d89-5cb64160c4d7
-- title:
--   D: ip lg F fun Eq
-- statement:
--   The D construction uses the ip lg F fun Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L121-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/IpNormPowSubPowLe.lean#L121-L139

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

theorem Formalism.L2.Th1.D.ip_lgF_funEq {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) (hlK : (l : K) ≠ 0)
    (hq : l ^ 2 ≠ 0) :
    (lgF K l : MvPowerSeries Unit K) -
      (l : K)⁻¹ • MvPowerSeries.expand (l ^ 2) hq (lgF K l : MvPowerSeries Unit K) =
      MvPowerSeries.X () := by sorry
