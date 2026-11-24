-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mem_decomposition_subgroup_iff
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.mem_decomposition_subgroup_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:58.550271+00:00
-- url     : https://prove2.me/theorems/ded72d6e-7e59-435f-a052-8ed0dffdae35
-- title:
--   Model Embedding: mem decomposition subgroup iff
-- statement:
--   The Model Embedding construction uses the mem decomposition subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L47-L50

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.mem_decomposition_subgroup_iff {n : ℕ} {g : GalL n} : g ∈ D2 n ↔ g.2.2 = 1 := by sorry
