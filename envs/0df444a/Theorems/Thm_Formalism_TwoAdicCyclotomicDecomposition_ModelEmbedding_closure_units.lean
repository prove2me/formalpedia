-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_closure_units
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.closure_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:52.480884+00:00
-- url     : https://prove2.me/theorems/18761703-e82a-47f0-aa33-955fc2724770
-- title:
--   Model Embedding: closure units
-- statement:
--   The Model Embedding construction uses the closure units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L155-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L155-L182

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.closure_units (k : ℕ) :
    Subgroup.closure {(-1 : (ZMod (2 ^ (k + 2)))ˣ), u5 (k + 2)} = ⊤ := by sorry
