-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_KF_exists_ext
-- name    : Formalism.L2.Th1.D.KF.exists_ext
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:47.124831+00:00
-- url     : https://prove2.me/theorems/885d40e6-f52d-4a61-904c-338a41061074
-- title:
--   KF: exists ext
-- statement:
--   The KF construction uses the exists ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L288-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusExtensionOnInclusion.lean#L288-L308

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

theorem Formalism.L2.Th1.D.KF.exists_ext (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1)
    (g : ringB l →+* ℂ_[l]) (hg : ∀ x, g x ∈ ringB l) :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, ∀ (x : MaximalUnramifiedExtension l) (hx : (x : ℂ_[l]) ∈ ringB l),
      (σ x : ℂ_[l]) = g ⟨x, hx⟩ := by sorry
