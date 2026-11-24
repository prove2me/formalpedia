-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_five_units_two_pow
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_five_units_two_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:31.426791+00:00
-- url     : https://prove2.me/theorems/81138e02-19b8-41fc-b231-feab0bbb4330
-- title:
--   Model Embedding: order Of five units two pow
-- statement:
--   The Model Embedding construction uses the order Of five units two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L115-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L115-L138

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
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_five_units_two_pow (k : ℕ) : orderOf (u5 (k + 2)) = 2 ^ k := by sorry
