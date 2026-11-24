-- Prove2me | Theorems.Thm_Formalism_GM_M_good_tie
-- name    : Formalism.GM.M.good_tie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:26.801248+00:00
-- url     : https://prove2.me/theorems/57c8ddba-75de-4591-bcb8-8896a636caca
-- title:
--   M: good tie
-- statement:
--   The M construction uses the good tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L433-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L433-L451

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

theorem Formalism.GM.M.good_tie (i : Fin (t + 1)) (e : MvPolynomial (BVar N r t) ℚ_[p]) (he : SFree (scalS N r t) e) :
    Good (scalS N r t) (X (scalZ N r t i) * X (scalS N r t i) + e) (Pi.single i 1)
      (Finsupp.single (scalZ N r t i) 1 + Finsupp.single (scalS N r t i) 1) := by sorry
