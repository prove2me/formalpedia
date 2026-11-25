-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_shift_apply
-- name    : CompanionTheory.Zuck.shift_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:10:52.80041+00:00
-- url     : https://prove2.me/theorems/90d3f1f2-6c4d-5720-9601-c0db9c492259
-- title:
--   Zuck: shift apply
-- statement:
--   The Zuck construction uses the shift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L84-L86

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

theorem CompanionTheory.Zuck.shift_apply (b : Bool) (μ : Fin n → ℝ) (s a : Fin n) :
    shift b μ s a = μ a + if a = s then (if b then -1 else 1) else 0 := by sorry
