-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_index
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:43.386382+00:00
-- url     : https://prove2.me/theorems/002f4930-3193-41d6-ad59-84d4f14b5fc9
-- title:
--   Cycle Type Finite Order: exists index
-- statement:
--   The Cycle Type Finite Order construction uses the exists index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L91-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L91-L111

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_index (hf : GoodPoly N f) : ∃ (r : Fin N → Fbar g) (σ : Equiv.Perm (Fin N)),
    Function.Injective r ∧ Finset.univ.val.map r = rootsBar f ∧ (∀ i, r (σ i) = r i ^ g) := by sorry
