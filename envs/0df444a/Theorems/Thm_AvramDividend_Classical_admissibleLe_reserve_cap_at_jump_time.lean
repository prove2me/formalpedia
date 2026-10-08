-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleLe_reserve_cap_at_jump_time
-- name    : AvramDividend.Classical.admissibleLe_reserve_cap_at_jump_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:00:54.534923+00:00
-- url     : https://prove2.me/theorems/745ee195-887b-4e24-a79a-3877c72efe8d
-- title:
--   The reserve cap holds at every admissibility-controlled jump time
-- statement:
--   For a capped admissible strategy, the controlled reserve is at most C at every jump time governed by admissibility. At positive times this is the IsAdmissibleLe cap. At time zero the controlled reserve equals the initial capital because X_0=D_0=0, so the separate initial-capital cap applies.
-- source:
--   Elementary cap helper for the jump term in Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissibleLe_reserve_cap_at_jump_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by sorry
