-- Prove2me | Theorems.Thm_Formalism_Q3_hostIn_card
-- name    : Formalism.Q3.hostIn_card
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:54.18475+00:00
-- url     : https://prove2.me/theorems/33e1b75e-c1a5-42f2-987f-5331d52d81bf
-- title:
--   Q3: host In card
-- statement:
--   The Q3 construction uses the host In card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L16-L24

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3

theorem Formalism.Q3.hostIn_card (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (P.inertia Gal(E/ℚ)) = P.ramificationIdx ℤ := by sorry
