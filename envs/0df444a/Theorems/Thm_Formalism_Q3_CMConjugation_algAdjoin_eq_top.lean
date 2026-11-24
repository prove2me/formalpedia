-- Prove2me | Theorems.Thm_Formalism_Q3_CMConjugation_algAdjoin_eq_top
-- name    : Formalism.Q3.CMConjugation.algAdjoin_eq_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:11.582482+00:00
-- url     : https://prove2.me/theorems/876b66ed-297f-4095-9613-c1ec12152b67
-- title:
--   CMConjugation: alg Adjoin eq top
-- statement:
--   The CMConjugation construction uses the alg Adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean#L53-L56

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

theorem Formalism.Q3.CMConjugation.algAdjoin_eq_top (hα : IsHost q α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by sorry
