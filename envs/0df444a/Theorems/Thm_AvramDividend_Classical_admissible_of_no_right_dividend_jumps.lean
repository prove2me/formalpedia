-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_of_no_right_dividend_jumps
-- name    : AvramDividend.Classical.admissible_of_no_right_dividend_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:19:16.67004+00:00
-- url     : https://prove2.me/theorems/851560bc-0848-48a8-ad92-8ade90393f97
-- title:
--   Right-continuous dividend strategies with no right dividend jumps are admissible
-- statement:
--   Let X be a spectrally negative Levy process, x>=0 initial reserve, and D an adapted, nondecreasing, left-continuous dividend strategy. If the strict right-limit dividend amount equals the current dividend amount at all paths and times, then the right jump in dividends is zero. Before ruin the reserve must be nonnegative by the defining infimum over all negative-reserve times; at time zero the reserve equals x. Thus D is admissible.
-- source:
--   General bridge for the AvramDividend capped-value witness. Avoid repeatedly reproving nonnegative reserve before ruin or t=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_of_no_right_dividend_jumps {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hr : ∀ ω (t : ℝ≥0), rightLimit D t ω = D t ω) :
    IsAdmissible X x D := by
  sorry
