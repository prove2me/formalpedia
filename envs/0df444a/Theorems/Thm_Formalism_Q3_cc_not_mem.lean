-- Prove2me | Theorems.Thm_Formalism_Q3_cc_not_mem
-- name    : Formalism.Q3.cc_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:42.61205+00:00
-- url     : https://prove2.me/theorems/773a78a6-d1f4-427e-b1fb-15f201169387
-- title:
--   Q3: cc not mem
-- statement:
--   The Q3 construction uses the cc not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/KroneckerMeaning.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/KroneckerMeaning.lean#L36-L47

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.Q3
open ZMod

theorem Formalism.Q3.cc_not_mem (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by sorry
