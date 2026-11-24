-- Prove2me | Theorems.Thm_Formalism_Q3_CMConjugation_sigma_alpha
-- name    : Formalism.Q3.CMConjugation.sigma_alpha
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:52.049749+00:00
-- url     : https://prove2.me/theorems/0158b1ab-a1f4-4c73-8e18-49ceec8cd6ce
-- title:
--   CMConjugation: sigma alpha
-- statement:
--   The CMConjugation construction uses the sigma alpha property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L25-L34

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

theorem Formalism.Q3.CMConjugation.sigma_alpha (hα : IsHost q α) (σ : Gal(E/ℚ)) (i : Fin 3) :
    σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := by sorry
