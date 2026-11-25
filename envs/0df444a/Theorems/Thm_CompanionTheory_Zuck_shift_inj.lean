-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_shift_inj
-- name    : CompanionTheory.Zuck.shift_inj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:19:58.01633+00:00
-- url     : https://prove2.me/theorems/9666ac5e-3dc0-5812-bed4-3586378179aa
-- title:
--   Zuck: shift inj
-- statement:
--   The Zuck construction uses the shift inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L125-L130

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

theorem CompanionTheory.Zuck.shift_inj (b : Bool) (μ : Fin n → ℝ) : Function.Injective (shift b μ) := by sorry
