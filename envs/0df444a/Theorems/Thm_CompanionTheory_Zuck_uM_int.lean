-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_uM_int
-- name    : CompanionTheory.Zuck.uM_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:55.824809+00:00
-- url     : https://prove2.me/theorems/c1471ef3-b4b0-49b5-95c0-623d2bafcc5f
-- title:
--   Zuck: u M int
-- statement:
--   The Zuck construction uses the u M int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L86-L88

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

theorem CompanionTheory.Zuck.uM_int (F : FRep k r) (g : Mx k r) : uM F.ι * F.ρ g = ((triv k r).tens F).ρ g * uM F.ι := by sorry
