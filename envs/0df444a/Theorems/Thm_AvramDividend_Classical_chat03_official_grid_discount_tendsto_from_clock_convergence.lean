-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_official_grid_discount_tendsto_from_clock_convergence
-- name    : AvramDividend.Classical.chat03_official_grid_discount_tendsto_from_clock_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:24:54.178657+00:00
-- url     : https://prove2.me/theorems/11c54f4f-11c1-490f-be6b-2698ec8e8991
-- title:
--   Official upper-first Lévy grid discount converges whenever grid clocks converge and infinite upper passage remains infinite on grids
-- statement:
--   For the official exact strict upper and lower first-passage times of a spectrally negative Lévy process through separated barriers, suppose approximating ENNReal-valued grid passage clocks converge to each official clock. If no strict upper crossing in continuous time implies that every sampled upper grid clock is infinite, then the exact conditional upper-first discounted grid payoff converges pointwise to the official upper-first discounted payoff. The official no-finite-ties theorem supplies the necessary exclusion of equal finite clocks; the accepted generic all-case grid payoff convergence theorem handles strict upper-first, strict lower-first and both-infinite outcomes. No new stochastic martingale assumptions are made.
-- source:
--   Proved official no finite passage ties a9c87fbc-54b8-40cd-b082-ae3e90e996a9 and proved all-outcomes grid reward convergence d25d182c-7361-4d99-8c7f-d09de64e2a00.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_official_grid_discount_tendsto_from_clock_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop
      (𝓝 (twoSidedExitUpTime X upper ω)))
    (hd : Tendsto downGrid atTop
      (𝓝 (twoSidedExitDownTime X lower ω)))
    (hNoUpGrid : twoSidedExitUpTime X upper ω = ∞ →
      ∀ n : ℕ, upGrid n = ∞) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by sorry
