-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_stable_of_subSum
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.stable_of_subSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:57.900686+00:00
-- url     : https://prove2.me/theorems/941502a0-dd0b-43a3-b2d8-a1d131ea134b
-- title:
--   Cycle Type Finite Order: stable of sub Sum
-- statement:
--   The Cycle Type Finite Order construction uses the stable of sub Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L361-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L361-L390

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.stable_of_subSum (hLi : Function.Injective L) {a : ℕ}
    (h : Formalism.GaloisIrreducibility.IsSubSum ((blocks σ L).val.map Finset.card) a) :
    ∃ A : Finset α, (∀ i ∈ A, σ i ∈ A) ∧ A.card = a := by sorry
