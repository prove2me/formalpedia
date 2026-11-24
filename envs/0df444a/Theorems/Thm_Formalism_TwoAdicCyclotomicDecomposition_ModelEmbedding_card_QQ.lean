-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_QQ
-- name    : Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_QQ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:52.929408+00:00
-- url     : https://prove2.me/theorems/32e3a753-2308-40f0-bbce-d9d5194e163d
-- title:
--   Model Embedding: card QQ
-- statement:
--   The Model Embedding construction uses the card QQ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L244-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean#L244-L248

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

theorem Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_QQ (n : ℕ) :
    Nat.card ((GalL n ⧸ zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ zpowers (JJ n)) →* _).range) = (KK n).index := by sorry
