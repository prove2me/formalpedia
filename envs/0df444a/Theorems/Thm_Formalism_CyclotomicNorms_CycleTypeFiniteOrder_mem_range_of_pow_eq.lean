-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_range_of_pow_eq
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_range_of_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:23.034292+00:00
-- url     : https://prove2.me/theorems/4ec2edf7-6550-4950-b550-3546849181d5
-- title:
--   Cycle Type Finite Order: mem range of pow eq
-- statement:
--   The Cycle Type Finite Order construction uses the mem range of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L51-L53

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

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_range_of_pow_eq (c : Fbar g) (hc : c ^ g = c) :
    c ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by sorry
