-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_sum_val_eq_biUnion
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.sum_val_eq_biUnion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:47.501666+00:00
-- url     : https://prove2.me/theorems/61b25bdb-fd89-4f6b-8822-fb05873ff90b
-- title:
--   Cycle Type Finite Order: sum val eq bi Union
-- statement:
--   The Cycle Type Finite Order construction uses the sum val eq bi Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L311-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L311-L326

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.sum_val_eq_biUnion (I : Finset (Finset K))
    (hI : ∀ S ∈ I, ∀ T ∈ I, S ≠ T → Disjoint S T) :
    ∑ S ∈ I, S.val = (I.biUnion id).val := by sorry
