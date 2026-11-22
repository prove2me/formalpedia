-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_five_mod_four
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.unitsMap_five_mod_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:52:07.335391+00:00
-- url     : https://prove2.me/theorems/3e672afe-cb0c-4c46-adf4-c3a1e07cc933
-- title:
--   Model Embedding: units Map five mod four
-- statement:
--   The Model Embedding construction uses the units Map five mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L140-L148

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.unitsMap_five_mod_four (n : ℕ) (h : 4 ∣ 2 ^ n) : ZMod.unitsMap h (u5 n) = 1 := by sorry
