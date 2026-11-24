-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
-- name    : Formalism.L2.Th1.D.KF.norm_l_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:53:41.091863+00:00
-- url     : https://prove2.me/theorems/6a31087a-0ea0-463c-8b0a-b04cd178ec80
-- title:
--   KF: norm l eq
-- statement:
--   The KF construction uses the norm l eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L18-L23

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]

theorem Formalism.L2.Th1.D.KF.norm_l_eq : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by sorry
