-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_le_ramificationIdx
-- name    : Formalism.TwoAdicCyclotomicDecomposition.le_ramificationIdx
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:36.706331+00:00
-- url     : https://prove2.me/theorems/c89ac60e-843c-41eb-be2a-c6c9167ada4a
-- title:
--   Two Adic Cyclotomic Decomposition: le ramification Idx
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the le ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L107-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L107-L148

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

theorem Formalism.TwoAdicCyclotomicDecomposition.le_ramificationIdx {L : Type} [Field L] [NumberField L] (k : ℕ) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    2 ^ k ≤ P.ramificationIdx ℤ := by sorry
