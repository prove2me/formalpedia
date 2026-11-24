-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KF_norm_pow_add_lt_one
-- name    : Formalism.L2.Th1.D.KF.norm_pow_add_lt_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:27.776894+00:00
-- url     : https://prove2.me/theorems/5413a929-61c3-4054-bd34-2972d0e3faba
-- title:
--   KF: norm pow add lt one
-- statement:
--   The KF construction uses the norm pow add lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L44-L54

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
variable {l}

theorem Formalism.L2.Th1.D.KF.norm_pow_add_lt_one {a b : ℂ_[l]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖a ^ l + (l : ℂ_[l]) * b‖ < 1 := by sorry
