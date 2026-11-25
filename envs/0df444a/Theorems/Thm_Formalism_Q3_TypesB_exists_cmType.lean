-- Prove2me | Theorems.Thm_Formalism_Q3_TypesB_exists_cmType
-- name    : Formalism.Q3.TypesB.exists_cmType
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:10.467614+00:00
-- url     : https://prove2.me/theorems/1224e33f-feda-41e3-8784-c4a81abef407
-- title:
--   Types B: exists cm Type
-- statement:
--   The Types B construction uses the exists cm Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L24-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L24-L53

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.Q3
open Formalism.Q3.TypesB
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

theorem Formalism.Q3.TypesB.exists_cmType [Fintype G] (hc1 : c ≠ 1) (hc : c * c = 1) :
    ∃ H : Finset G, IsCMTypeG c H ∧ 1 ∈ H := by sorry
