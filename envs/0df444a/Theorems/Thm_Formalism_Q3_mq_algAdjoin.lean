-- Prove2me | Theorems.Thm_Formalism_Q3_mq_algAdjoin
-- name    : Formalism.Q3.mq_algAdjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:02.674403+00:00
-- url     : https://prove2.me/theorems/4320c6d0-49f4-499b-8714-9bf01650b430
-- title:
--   Q3: mq alg Adjoin
-- statement:
--   The Q3 construction uses the mq alg Adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/MQGalois.lean#L46-L49

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}

theorem Formalism.Q3.mq_algAdjoin (h : IsMQ a α) : Algebra.adjoin ℚ (Set.range α) = ⊤ := by sorry
