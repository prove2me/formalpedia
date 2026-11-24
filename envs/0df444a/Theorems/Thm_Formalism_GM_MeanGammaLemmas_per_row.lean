-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_per_row
-- name    : Formalism.GM.MeanGammaLemmas.per_row
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:37.046033+00:00
-- url     : https://prove2.me/theorems/4b7ff091-2096-4e05-bac6-372ce2e18984
-- title:
--   Mean Gamma Lemmas: per row
-- statement:
--   The Mean Gamma Lemmas construction uses the per row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L266-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L266-L307

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset

theorem Formalism.GM.MeanGammaLemmas.per_row (p : ℕ) [hp : Fact p.Prime] (a r S o z e cI : ℕ) (κ C : ℝ)
    (heo : e ≤ o) (ho : o ≤ 2 * a) (hS : S ≤ 2 * a) (hz : z ≤ 2 * a) (hr : 1 ≤ r)
    (hκ : 12 * (Real.logb p (8 * a + r) + 1) ≤ κ) (hcI : (cI : ℝ) ≤ C * κ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ (⌈κ⌉₊ + cI) * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ ≤
      (C + 3) * κ := by sorry
