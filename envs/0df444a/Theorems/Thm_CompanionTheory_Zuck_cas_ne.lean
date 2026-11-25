-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_cas_ne
-- name    : CompanionTheory.Zuck.cas_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:38:01.456246+00:00
-- url     : https://prove2.me/theorems/9aea6fea-52b7-52b0-be1a-4260af6b20dc
-- title:
--   Zuck: cas ne
-- statement:
--   The Zuck construction uses the cas ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L113-L123

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

theorem CompanionTheory.Zuck.cas_ne {μ : Fin n → ℝ} (hμ : StrictAnti μ) (b : Bool) (s t : Fin n) :
    (casG (shift b (shift b μ s) t) : ℂ) ≠ 2 * (casG (shift b μ s) : ℂ) - (casG μ : ℂ) := by sorry
