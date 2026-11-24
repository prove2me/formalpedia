-- Prove2me | Theorems.Thm_Formalism_Q3_kron_odd
-- name    : Formalism.Q3.kron_odd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:24.745581+00:00
-- url     : https://prove2.me/theorems/64a3741f-64d1-4206-bc13-8d5efd701b77
-- title:
--   Q3: kron odd
-- statement:
--   The Q3 construction uses the kron odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/KroneckerMeaning.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/KroneckerMeaning.lean#L8-L18

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

theorem Formalism.Q3.kron_odd (q p : ℕ) (hq4 : q % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by sorry
