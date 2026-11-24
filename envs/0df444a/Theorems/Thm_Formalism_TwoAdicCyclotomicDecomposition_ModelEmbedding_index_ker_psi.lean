-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_index_ker_psi
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.index_ker_psi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:03.220471+00:00
-- url     : https://prove2.me/theorems/343ffbfb-aac9-450d-b4ec-6812bd131996
-- title:
--   Model Embedding: index ker psi
-- statement:
--   The Model Embedding construction uses the index ker psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L404-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L404-L406

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
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.index_ker_psi (k : ℕ) : (psi k).ker.index = 8 := by sorry
