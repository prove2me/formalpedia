-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_JJ
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_JJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:58.483798+00:00
-- url     : https://prove2.me/theorems/4080c3ac-772c-46bb-bd8e-29b52b17ee14
-- title:
--   Model Embedding: order Of JJ
-- statement:
--   The Model Embedding construction uses the order Of JJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L38-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L38-L38

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_JJ (n : ℕ) : orderOf (JJ n) = 2 := by sorry
