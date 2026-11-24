-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_eq_two_of_mul_self_eq_one
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_eq_two_of_mul_self_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:21.463361+00:00
-- url     : https://prove2.me/theorems/e347f5e5-6664-4d44-a413-5e98f468ee10
-- title:
--   Model Embedding: order Of eq two of mul self eq one
-- statement:
--   The Model Embedding construction uses the order Of eq two of mul self eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L184-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L184-L184

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_eq_two_of_mul_self_eq_one {n : ℕ} (g : GalL n) (h : g * g = 1) (h1 : g ≠ 1) : orderOf g = 2 := by sorry
