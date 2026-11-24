-- Prove2me | Theorems.Thm_Formalism_Q3_TypesB_mem_image_cmul
-- name    : Formalism.Q3.TypesB.mem_image_cmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:23.709041+00:00
-- url     : https://prove2.me/theorems/8fa97c31-8145-4ad8-a01b-3919eaf761ff
-- title:
--   Types B: mem image cmul
-- statement:
--   The Types B construction uses the mem image cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L15-L22

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

theorem Formalism.Q3.TypesB.mem_image_cmul (hc : c * c = 1) (X : Finset G) (g : G) :
    g ∈ X.image (fun x => c * x) ↔ c * g ∈ X := by sorry
