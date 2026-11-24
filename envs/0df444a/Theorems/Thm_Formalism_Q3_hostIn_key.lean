-- Prove2me | Theorems.Thm_Formalism_Q3_hostIn_key
-- name    : Formalism.Q3.hostIn_key
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:08.517101+00:00
-- url     : https://prove2.me/theorems/3dee1681-d33a-48d1-8853-9de4ddbb0eac
-- title:
--   Q3: host In key
-- statement:
--   The Q3 construction uses the host In key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L44-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L44-L88

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

theorem Formalism.Q3.hostIn_key (hG : MQGalois) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) (j : Fin 3) (hj : galSign α σ j = -1) :
    (p : ℤ) ∣ (q j : ℤ) := by sorry
