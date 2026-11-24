-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KF_jBK_inj
-- name    : Formalism.L2.Th1.D.KF.jBK_inj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:38.673253+00:00
-- url     : https://prove2.me/theorems/51032220-bc80-4c53-bfcd-d17a8c47c252
-- title:
--   KF: j BK inj
-- statement:
--   The KF construction uses the j BK inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L246-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L246-L250

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
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)

theorem Formalism.L2.Th1.D.KF.jBK_inj (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) :
    Function.Injective (jBK hB) := by sorry
