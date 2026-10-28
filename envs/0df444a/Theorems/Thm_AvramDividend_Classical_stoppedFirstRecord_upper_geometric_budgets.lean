-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
-- name    : AvramDividend.Classical.stoppedFirstRecord_upper_geometric_budgets
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T20:20:51.305171+00:00
-- url     : https://prove2.me/theorems/bae08f81-eb5e-447a-8720-876d1a31bd60
-- title:
--   Upper geometric record budgets for the stopped renewal upper bound
-- statement:
--   For a standing spectrally negative Levy model with q-scale function W, at a positive barrier a and mesh eps with W(a+eps) strictly above W(a), the killed upper-record grid of width eps (up-crossing clocks below the ruin time, weighted by eps-discounted factors) dominates the stopped payment integral almost everywhere and contracts geometrically with ratio W(a)/W(a+eps) in expectation. This is the exact missing budget package consumed by the proved bridge barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step on the road to the stopped renewal upper bound (Proposition 1 proof path), mirroring the existing lower-budget theorem stoppedFirstRecord_lower_geometric_budgets on the upper grid.
-- source:
--   Upper-grid budget-existence stage of the stopped-renewal upper-bound argument for Proposition 1 (barrier_strategy_value); extracted as an independently useful lemma so the parent close stays within submission caps. Mirrors the existing Open stoppedFirstRecord_lower_geometric_budgets on the upper (a+eps) grid with the definitional w-shape consumed by the proved bridge c481fcb6 (via a8bd0ad1). All referenced declarations (twoSidedExitUpTime, barrierRuinTime, paymentTimes, dividendMeasure, runningSup) appear verbatim in authoritative in-mission statements read this turn.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem stoppedFirstRecord_upper_geometric_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) :
    ∃ w : ℕ → Ω → ℝ≥0∞,
      (∀ n ω, w n ω =
        if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal
            (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
        else 0)
      ∧ (∀ᵐ ω ∂P,
        (∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
      ∧ (∀ n : ℕ,
        (∫⁻ ω, w (n + 1) ω ∂P) ≤
          ENNReal.ofReal (W a / W (a + ε)) *
            (∫⁻ ω, w n ω ∂P)) := by sorry

end AvramDividend.Classical
