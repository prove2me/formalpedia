-- Prove2me | Theorems.Thm_Formalism_Q3_hostIn_ram_ne_one
-- name    : Formalism.Q3.hostIn_ram_ne_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:06.3996+00:00
-- url     : https://prove2.me/theorems/e2189078-71b2-4706-ae49-39e1acf28461
-- title:
--   Q3: host In ram ne one
-- statement:
--   The Q3 construction uses the host In ram ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L90-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L90-L111

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

theorem Formalism.Q3.hostIn_ram_ne_one (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (i : Fin 3) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(q i : ℤ)})] :
    P.ramificationIdx ℤ ≠ 1 := by sorry
