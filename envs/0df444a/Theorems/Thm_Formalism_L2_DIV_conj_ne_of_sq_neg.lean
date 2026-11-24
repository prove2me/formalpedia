-- Prove2me | Theorems.Thm_Formalism_L2_DIV_conj_ne_of_sq_neg
-- name    : Formalism.L2.DIV.conj_ne_of_sq_neg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:19.338001+00:00
-- url     : https://prove2.me/theorems/2d5f4788-4be9-4044-b86e-c47c6fd0dcaa
-- title:
--   DIV: conj ne of sq neg
-- statement:
--   The DIV construction uses the conj ne of sq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L18-L22

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues

theorem Formalism.L2.DIV.conj_ne_of_sq_neg {w : ℂ} {r : ℝ} (hr : r < 0) (hw : w ^ 2 = (r : ℂ)) : starRingEnd ℂ w ≠ w := by sorry
