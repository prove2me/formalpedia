-- Prove2me | Theorems.Thm_Formalism_Q3_CMConjugation_alpha_ne_zero
-- name    : Formalism.Q3.CMConjugation.alpha_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:00.953677+00:00
-- url     : https://prove2.me/theorems/b046cb45-842d-4256-b1f8-e388b04766ed
-- title:
--   CMConjugation: alpha ne zero
-- statement:
--   The CMConjugation construction uses the alpha ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L19-L23

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

theorem Formalism.Q3.CMConjugation.alpha_ne_zero (hq : Hyp3 q) (hα : IsHost q α) (i : Fin 3) : α i ≠ 0 := by sorry
