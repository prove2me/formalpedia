-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_ne_zero_of_mem
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:18.653725+00:00
-- url     : https://prove2.me/theorems/d0488629-49ef-45e7-89be-03f395eb7ef8
-- title:
--   Cycle Type Finite Order: ne zero of mem
-- statement:
--   The Cycle Type Finite Order construction uses the ne zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L82-L86

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ≠ 0 := by sorry
