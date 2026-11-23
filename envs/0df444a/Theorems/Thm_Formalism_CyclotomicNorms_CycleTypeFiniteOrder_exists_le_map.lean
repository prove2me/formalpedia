-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_le_map
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_le_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:04.616061+00:00
-- url     : https://prove2.me/theorems/625171d0-a526-4eb4-86e4-483886314fb7
-- title:
--   Cycle Type Finite Order: exists le map
-- statement:
--   The Cycle Type Finite Order construction uses the exists le map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L343-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L343-L359

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_exists_le_map

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_le_map {β γ : Type*} (m : Multiset β) (f : β → γ) (s : Multiset γ)
    (h : s ≤ m.map f) : ∃ t ≤ m, t.map f = s := by sorry
