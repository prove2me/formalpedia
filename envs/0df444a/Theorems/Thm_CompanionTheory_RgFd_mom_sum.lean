-- Prove2me | Theorems.Thm_CompanionTheory_RgFd_mom_sum
-- name    : CompanionTheory.RgFd.mom_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:29.624473+00:00
-- url     : https://prove2.me/theorems/73dec7e4-e81a-4575-be0c-e2b9824129a3
-- title:
--   Rg Fd: mom sum
-- statement:
--   The Rg Fd construction uses the mom sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/FormalDegrees/ArchimedeanFormalDegrees/MomentRecursion/MomStep.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/FormalDegrees/ArchimedeanFormalDegrees/MomentRecursion/MomStep.lean#L34-L48

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd

theorem CompanionTheory.RgFd.mom_sum {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := by sorry
