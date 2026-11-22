-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_intCast_mem_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.two_intCast_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:54:04.644593+00:00
-- url     : https://prove2.me/theorems/b159d587-d6e8-4e1c-9b35-91074a277cb5
-- title:
--   Two Adic Cyclotomic Decomposition: two int Cast mem iff
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the two int Cast mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L13-L17

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.two_intCast_mem_iff {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(2 : ℤ)})] (m : ℤ) :
    (m : 𝓞 L) ∈ P ↔ (2 : ℤ) ∣ m := by sorry
