-- Prove2me | Theorems.Thm_Formalism_Q3_CMRootsOfUnity_not_sq_in_E
-- name    : Formalism.Q3.CMRootsOfUnity.not_sq_in_E
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:11.62274+00:00
-- url     : https://prove2.me/theorems/c5bf694c-4dd0-4c17-812e-e8142c55369d
-- title:
--   CMRoots Of Unity: not sq in E
-- statement:
--   The CMRoots Of Unity construction uses the not sq in E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostMu.lean#L54-L65

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
variable {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}

theorem Formalism.Q3.CMRootsOfUnity.not_sq_in_E (hK : MQKummer) (hq : Hyp3 q) (hα : IsHost q α) (d : ℤ) (hd : d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) : ¬ IsSquare (d : E) := by sorry
