-- Prove2me | Theorems.Thm_Formalism_GM_TM_lg_nonneg
-- name    : Formalism.GM.TM.lg_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:45.534236+00:00
-- url     : https://prove2.me/theorems/222b1515-8aba-4c45-bebc-79160fe6dd86
-- title:
--   TM: lg nonneg
-- statement:
--   The TM construction uses the lg nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L598-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L598-L606

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

theorem Formalism.GM.TM.lg_nonneg (p a r : ℕ) [Fact p.Prime] (hr : 2 ≤ r) : 0 ≤ lgV2 p a r := by sorry
