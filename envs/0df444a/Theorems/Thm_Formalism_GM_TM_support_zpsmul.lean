-- Prove2me | Theorems.Thm_Formalism_GM_TM_support_zpsmul
-- name    : Formalism.GM.TM.support_zpsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:00.387862+00:00
-- url     : https://prove2.me/theorems/9a41ad55-4ab2-4953-92ee-72224781015e
-- title:
--   TM: support zpsmul
-- statement:
--   The TM construction uses the support zpsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L298-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L298-L305

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

theorem Formalism.GM.TM.support_zpsmul (a : ℤ_[p]) (ha : a ≠ 0) (x : MvPolynomial σ ℚ_[p]) : (a • x).support = x.support := by sorry
