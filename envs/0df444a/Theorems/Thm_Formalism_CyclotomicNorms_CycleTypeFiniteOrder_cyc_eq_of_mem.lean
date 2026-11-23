-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc_eq_of_mem
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.cyc_eq_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:52.411743+00:00
-- url     : https://prove2.me/theorems/1ff6b8f9-b39a-4b00-94c8-95f86eb35f78
-- title:
--   Cycle Type Finite Order: cyc eq of mem
-- statement:
--   The Cycle Type Finite Order construction uses the cyc eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L293-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L293-L298

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.cyc_eq_of_mem {i j k : α} (hj : k ∈ cyc σ i) (hk : k ∈ cyc σ j) : cyc σ i = cyc σ j := by sorry
