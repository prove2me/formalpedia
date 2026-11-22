-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_unitsTwoPow
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_unitsTwoPow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:53.914269+00:00
-- url     : https://prove2.me/theorems/d62490d7-2555-4a52-b9a6-932cb968151e
-- title:
--   Model Embedding: card units Two Pow
-- statement:
--   The Model Embedding construction uses the card units Two Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_unitsTwoPow (n : ℕ) (hn : 1 ≤ n) : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by sorry
