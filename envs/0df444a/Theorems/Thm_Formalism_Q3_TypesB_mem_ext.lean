-- Prove2me | Theorems.Thm_Formalism_Q3_TypesB_mem_ext
-- name    : Formalism.Q3.TypesB.mem_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:20.41325+00:00
-- url     : https://prove2.me/theorems/87213783-b378-4cea-975f-a779b3d51968
-- title:
--   Types B: mem ext
-- statement:
--   The Types B construction uses the mem ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesB.lean#L57-L60

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

theorem Formalism.Q3.TypesB.mem_ext (hc : c * c = 1) (H S : Finset G) (x : G) :
    x ∈ ext c H S ↔ x ∈ S ∨ (c * x ∈ H ∧ c * x ∉ S) := by sorry
