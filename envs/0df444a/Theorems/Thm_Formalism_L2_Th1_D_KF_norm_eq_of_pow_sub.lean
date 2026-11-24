-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KF_norm_eq_of_pow_sub
-- name    : Formalism.L2.Th1.D.KF.norm_eq_of_pow_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:29.936324+00:00
-- url     : https://prove2.me/theorems/0b8c513a-4688-405f-80ad-cf73b5ed7cd5
-- title:
--   KF: norm eq of pow sub
-- statement:
--   The KF construction uses the norm eq of pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L56-L68

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

theorem Formalism.L2.Th1.D.KF.norm_eq_of_pow_sub {a b : ℂ_[l]} {N : ℕ} (hN : N ≠ 0) (ha : ‖a‖ < 1)
    (h : a ^ (N + 1) - a = (l : ℂ_[l]) * b) : ‖a‖ = (l : ℝ)⁻¹ * ‖b‖ := by sorry
