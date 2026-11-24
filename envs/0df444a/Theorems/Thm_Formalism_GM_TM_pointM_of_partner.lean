-- Prove2me | Theorems.Thm_Formalism_GM_TM_pointM_of_partner
-- name    : Formalism.GM.TM.pointM_of_partner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:58.410507+00:00
-- url     : https://prove2.me/theorems/6933bd5b-95a2-4796-bd22-30271e0c98d7
-- title:
--   TM: point M of partner
-- statement:
--   The TM construction uses the point M of partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L905-L918
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L905-L918

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.GM.TM.pointM_of_partner (hBad : BadCrit) (hPart : PartnerM) : PointM := by sorry
