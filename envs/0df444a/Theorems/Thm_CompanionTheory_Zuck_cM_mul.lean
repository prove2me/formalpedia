-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_cM_mul
-- name    : CompanionTheory.Zuck.cM_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:23:08.998104+00:00
-- url     : https://prove2.me/theorems/ccf91af7-ad1f-5334-9f81-c0f27ec872d6
-- title:
--   Zuck: c M mul
-- statement:
--   The Zuck construction uses the c M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L47-L54

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

theorem CompanionTheory.Zuck.cM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Aᵀ * B = 1) :
    cM n * (A ⊗ₖ B) = (1 : Matrix Unit Unit ℂ) * cM n := by sorry
