-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_dec_iso
-- name    : CompanionTheory.Zuck.dec_iso
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:27:53.2608+00:00
-- url     : https://prove2.me/theorems/10d666fd-a259-5f21-820f-e7598602cfe2
-- title:
--   Zuck: dec iso
-- statement:
--   The Zuck construction uses the dec iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L56-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean#L56-L73

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
variable {O : Type 1} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

theorem CompanionTheory.Zuck.dec_iso (C : IsLinCat N Hom) {κ : Type} [Fintype κ] {X : O} {T T' : κ → O}
    (h : ∃ io pr, IsDec Hom X T io pr) (e : ∀ s, IsIso Hom (T s) (T' s)) : ∃ io pr, IsDec Hom X T' io pr := by sorry
