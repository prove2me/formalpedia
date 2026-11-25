-- Prove2me | Theorems.Thm_Formalism_Q3_key_dual
-- name    : Formalism.Q3.key_dual
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:16.433467+00:00
-- url     : https://prove2.me/theorems/f7de1939-65d0-4d66-837a-7e2ed768c136
-- title:
--   Q3: key dual
-- statement:
--   The Q3 construction uses the key dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/TypesA.lean#L39-L43

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

theorem Formalism.Q3.key_dual (hc : c * c = 1) {Φ : Finset G} (hΦ : IsCMTypeG c Φ) (σ : G) (h1 : σ ≠ 1)
    (h2 : σ ≠ c) : σ ∈ dualTypeG c Φ ↔ σ ∉ Φ := by sorry
