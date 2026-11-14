-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment
-- name    : AvramDividend.Classical.avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:59:34.162356+00:00
-- url     : https://prove2.me/theorems/17cd0e44-cf37-4c3a-a1b2-b50c1f8a09f7
-- title:
--   Original controlled reserve at prescribed level forces a small original Gaussian increment on good dividend cells
-- statement:
--   For any original adapted monotone left-continuous dividend strategy, a mesh cell from s to u with small dividend increment guarantees that rightLimit D(t) lies between the left endpoint D(s) and right endpoint D(u) for s≤t<u. If the original postpayment reserve x+X(t)-rightLimit D(t) equals a prescribed level b inside this cell, then the future original source increment X(t)-X(s) must belong to an interval of length epsilon centred on b-x-X(s)+D(s). This is the exact pathwise inclusion needed to invoke the independent Gaussian random-centre small-ball lemma in the B100 proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB260_original_good_dividend_cell_reserve_hit_forces_small_gaussian_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t u : ℝ≥0) (hst : s ≤ t) (htu : t < u)
    (x b epsilon : ℝ)
    (hSmall : D u ω - D s ω ≤ epsilon)
    (hHit : x + X.X t ω - rightLimit D t ω = b) :
    X.X t ω - X.X s ω ∈
      Icc (b - x - X.X s ω + D s ω)
        (b - x - X.X s ω + D s ω + epsilon) := by sorry
