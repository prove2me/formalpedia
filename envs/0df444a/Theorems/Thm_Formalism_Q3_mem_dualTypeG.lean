-- Prove2me | Theorems.Thm_Formalism_Q3_mem_dualTypeG
-- name    : Formalism.Q3.mem_dualTypeG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:29.969386+00:00
-- url     : https://prove2.me/theorems/3de5ddd4-67a9-4f3c-9e69-6fb3041f103c
-- title:
--   Q3: mem dual Type G
-- statement:
--   The Q3 construction uses the mem dual Type G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L15-L27

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_TypesA
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
variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

theorem Formalism.Q3.mem_dualTypeG (hc : c * c = 1) (Φ : Finset G) (g : G) :
    g ∈ dualTypeG c Φ ↔ g = 1 ∨ (c * g ∈ Φ ∧ c * g ≠ 1) := by sorry
