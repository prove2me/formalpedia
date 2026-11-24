-- Prove2me | Theorems.Thm_Formalism_GM_M_lv_last
-- name    : Formalism.GM.M.lv_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:33.604465+00:00
-- url     : https://prove2.me/theorems/f052b41f-b26c-4224-b814-5f9fa73634ca
-- title:
--   M: lv last
-- statement:
--   The M construction uses the lv last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L463-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L463-L464

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

theorem Formalism.GM.M.lv_last (j : Fin t → ℕ) (jp : ℕ) : lv j jp (Fin.last t) = jp := by sorry
