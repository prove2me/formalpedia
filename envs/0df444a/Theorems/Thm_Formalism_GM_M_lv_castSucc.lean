-- Prove2me | Theorems.Thm_Formalism_GM_M_lv_castSucc
-- name    : Formalism.GM.M.lv_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:32.359505+00:00
-- url     : https://prove2.me/theorems/ee21fe30-9d60-4e5d-b4c8-0cdb80dcde69
-- title:
--   M: lv cast Succ
-- statement:
--   The M construction uses the lv cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L460-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L460-L461

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {t : ℕ}

theorem Formalism.GM.M.lv_castSucc (j : Fin t → ℕ) (jp : ℕ) (k : Fin t) : lv j jp (Fin.castSucc k) = j k := by sorry
