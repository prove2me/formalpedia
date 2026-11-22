-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_exists_int_quad
-- name    : Formalism.TwoAdicCyclotomicDecomposition.exists_int_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:06:26.951945+00:00
-- url     : https://prove2.me/theorems/08df9165-e988-4655-9fb8-19b74a29a922
-- title:
--   Two Adic Cyclotomic Decomposition: exists int quad
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the exists int quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L19-L21

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

theorem Formalism.TwoAdicCyclotomicDecomposition.exists_int_quad {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = x + c) : ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = X + (c : 𝓞 L) := by sorry
