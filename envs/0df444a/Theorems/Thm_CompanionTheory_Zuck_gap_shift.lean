-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_gap_shift
-- name    : CompanionTheory.Zuck.gap_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:41.733393+00:00
-- url     : https://prove2.me/theorems/699e59dc-0f33-5358-ada4-c5ea19191c65
-- title:
--   Zuck: gap shift
-- statement:
--   The Zuck construction uses the gap shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L88-L98

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
variable {n : ℕ}

theorem CompanionTheory.Zuck.gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : GapAtLeast ε μ h) (b : Bool) (s : Fin n) :
    GapAtLeast ε (shift b μ s) (h - 1) := by sorry
