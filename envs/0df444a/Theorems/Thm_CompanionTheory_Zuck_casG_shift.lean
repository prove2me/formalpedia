-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_casG_shift
-- name    : CompanionTheory.Zuck.casG_shift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:01.90422+00:00
-- url     : https://prove2.me/theorems/06501ed7-7f86-40bf-a695-60b36acf29da
-- title:
--   Zuck: cas G shift
-- statement:
--   The Zuck construction uses the cas G shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L100-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L100-L111

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

theorem CompanionTheory.Zuck.casG_shift (b : Bool) (μ : Fin n → ℝ) (s : Fin n) :
    casG (shift b μ s) = casG μ + 2 * (if b then -1 else 1) * μ s + 1 := by sorry
