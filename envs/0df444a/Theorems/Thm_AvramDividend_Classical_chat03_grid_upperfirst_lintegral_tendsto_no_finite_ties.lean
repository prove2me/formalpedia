-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_no_finite_ties
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_no_finite_ties
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:20:02.874758+00:00
-- url     : https://prove2.me/theorems/e8dab1aa-30b2-4120-a6a8-d583dd5fe3bd
-- title:
--   Upper-first grid discount expectations converge with a.e. passage convergence, absence of finite ties and preserved non-exit
-- statement:
--   For a probability measure and nonnegative real q, let measurable upper and lower first-passage grid clocks converge almost everywhere to extended limiting clocks. Assume almost surely that any equality of the two limit clocks can only be at infinity, and that an infinite limiting upper clock implies every sampled upper grid clock is infinite. Then the ENNReal expectations of the exact grid upper-first discounted payoff converge to the exact limiting upper-first discounted expectation. The result combines the accepted pathwise all-outcomes convergence theorem with the accepted dominated-convergence theorem and the uniform one bound. It is the expectation convergence bridge for the two-sided stopped-scale identity, retaining finite-tie and no-exit requirements explicitly rather than hiding them.
-- source:
--   Accepted Chat03 pathwise all-outcome passage payoff convergence d25d182c-7361-4d99-8c7f-d09de64e2a00 and dominated lintegral convergence 0b09622e-3994-481a-9594-e3dbd3d76d29.

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_lintegral_tendsto_no_finite_ties
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q)
    (upGrid downGrid : ℕ → Ω → ℝ≥0∞)
    (up down : Ω → ℝ≥0∞)
    (hu : ∀ n, Measurable (upGrid n))
    (hd : ∀ n, Measurable (downGrid n))
    (hup : ∀ᵐ ω ∂P, Tendsto
      (fun n => upGrid n ω) atTop (𝓝 (up ω)))
    (hdown : ∀ᵐ ω ∂P, Tendsto
      (fun n => downGrid n ω) atTop (𝓝 (down ω)))
    (hfiniteTie : ∀ᵐ ω ∂P,
      up ω = down ω → up ω = ∞)
    (hNoUpGrid : ∀ᵐ ω ∂P,
      up ω = ∞ → ∀ n : ℕ, upGrid n ω = ∞) :
    Tendsto
      (fun n => ∫⁻ ω,
        if upGrid n ω < downGrid n ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (upGrid n ω))))
        else 0 ∂P)
      atTop
      (𝓝 (∫⁻ ω,
        if up ω < down ω then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P)) := by sorry
