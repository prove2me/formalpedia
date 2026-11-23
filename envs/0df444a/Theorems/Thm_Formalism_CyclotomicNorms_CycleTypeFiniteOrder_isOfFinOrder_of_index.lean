-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_isOfFinOrder_of_index
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOfFinOrder_of_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:06.972718+00:00
-- url     : https://prove2.me/theorems/e25ce303-2685-48e6-b866-3f55ff21f5a1
-- title:
--   Cycle Type Finite Order: is Of Fin Order of index
-- statement:
--   The Cycle Type Finite Order construction uses the is Of Fin Order of index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L121-L133

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
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOfFinOrder_of_index (hσ : ∀ i, r (σ i) = r i ^ g) (i : Fin N) (h0 : r i ≠ 0) :
    IsOfFinOrder (r i) := by sorry
