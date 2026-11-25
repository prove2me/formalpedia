-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_mAct_sub
-- name    : CompanionTheory.Zuck.mAct_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:02.867466+00:00
-- url     : https://prove2.me/theorems/d94fab46-7df9-5c56-866a-6767fb333f5d
-- title:
--   Zuck: m Act sub
-- statement:
--   The Zuck construction uses the m Act sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L30-L33

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
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
variable {k r : ℕ}

theorem CompanionTheory.Zuck.mAct_sub {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι' ι ℂ) :
    (mAct (A - B) : (ι → V) →ₗ[ℂ] _) = mAct A - mAct B := by sorry
