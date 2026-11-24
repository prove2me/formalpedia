-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_two_mul_le_of_dvd_ne
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.two_mul_le_of_dvd_ne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:43.321903+00:00
-- url     : https://prove2.me/theorems/b43136ad-b290-4195-9c8f-6856c0cf6a10
-- title:
--   Model Embedding: two mul le of dvd ne
-- statement:
--   The Model Embedding construction uses the two mul le of dvd ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L99-L104

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.two_mul_le_of_dvd_ne {a b : ℕ} (hb : 0 < b) (hd : a ∣ b) (hne : b ≠ a) : 2 * a ≤ b := by sorry
