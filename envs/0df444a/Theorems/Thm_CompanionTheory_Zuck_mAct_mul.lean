-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_mAct_mul
-- name    : CompanionTheory.Zuck.mAct_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:46.478967+00:00
-- url     : https://prove2.me/theorems/f1ebe713-afb7-5343-bb97-fe45e5dd0524
-- title:
--   Zuck: m Act mul
-- statement:
--   The Zuck construction uses the m Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L18-L22

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

theorem CompanionTheory.Zuck.mAct_mul {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) : (mAct (A * B) : (ι → V) →ₗ[ℂ] _) = mAct A ∘ₗ mAct B := by sorry
