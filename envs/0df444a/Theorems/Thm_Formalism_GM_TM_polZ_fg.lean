-- Prove2me | Theorems.Thm_Formalism_GM_TM_polZ_fg
-- name    : Formalism.GM.TM.polZ_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:07.372679+00:00
-- url     : https://prove2.me/theorems/185a7238-8b5a-4701-aca7-03d3cf83a6a7
-- title:
--   TM: pol Z fg
-- statement:
--   The TM construction uses the pol Z fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L511-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L511-L543

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

theorem Formalism.GM.TM.polZ_fg {K r : ℕ} (LLw : Letters K) : (PolZ p r LLw).FG := by sorry
