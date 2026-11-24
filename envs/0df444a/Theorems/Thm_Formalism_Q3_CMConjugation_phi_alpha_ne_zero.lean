-- Prove2me | Theorems.Thm_Formalism_Q3_CMConjugation_phi_alpha_ne_zero
-- name    : Formalism.Q3.CMConjugation.phi_alpha_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:59.513248+00:00
-- url     : https://prove2.me/theorems/6c9ddc81-9379-4155-aafc-7b902d93cdb1
-- title:
--   CMConjugation: phi alpha ne zero
-- statement:
--   The CMConjugation construction uses the phi alpha ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L75-L77

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

theorem Formalism.Q3.CMConjugation.phi_alpha_ne_zero (hq : Hyp3 q) (hα : IsHost q α) (φ : E →+* ℂ) (i : Fin 3) :
    φ (α i) ≠ 0 := by sorry
