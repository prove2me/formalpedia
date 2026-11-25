-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_mAct_smul
-- name    : CompanionTheory.Zuck.mAct_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:51.715205+00:00
-- url     : https://prove2.me/theorems/74b2eee6-7d97-5b48-93c9-747128b446cb
-- title:
--   Zuck: m Act smul
-- statement:
--   The Zuck construction uses the m Act smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L24-L28

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

theorem CompanionTheory.Zuck.mAct_smul {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ℂ) (A : Matrix ι' ι ℂ) :
    (mAct (a • A) : (ι → V) →ₗ[ℂ] _) = a • mAct A := by sorry
