-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_qMat_vr
-- name    : CompanionTheory.Zuck.qMat_vr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:29:10.385621+00:00
-- url     : https://prove2.me/theorems/de5c279b-69f0-46a8-a021-9acccc7bf900
-- title:
--   Zuck: q Mat vr
-- statement:
--   The Zuck construction uses the q Mat vr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L74-L82

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

theorem CompanionTheory.Zuck.qMat_vr (hS : StdD) (b : Bool) :
    qMat (vr k r b) (vr k r (!b)) = (-1 : ℂ) • ((cM _)ᵀ * cM _ : Matrix _ _ ℂ) := by sorry
