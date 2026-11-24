-- Prove2me | Theorems.Thm_Formalism_GM_M_sfree_pair
-- name    : Formalism.GM.M.sfree_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:06.0548+00:00
-- url     : https://prove2.me/theorems/9f042bdc-72df-49d0-89a5-22ef4ec018d2
-- title:
--   M: sfree pair
-- statement:
--   The M construction uses the sfree pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L453-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L453-L455

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

theorem Formalism.GM.M.sfree_pair (u w : Fin r → Fin (N + 1) × Fin r) :
    SFree (scalS N r t) (∑ c, X (Sum.inl (u c)) * X (Sum.inl (w c)) : MvPolynomial (BVar N r t) ℚ_[p]) := by sorry
