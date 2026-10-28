-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step
-- name    : AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_killed_grid_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:25:37.387981+00:00
-- url     : https://prove2.me/theorems/a8bd0ad1-f610-40fd-936c-4326c11c78da
-- title:
--   Actual killed first-record step estimates imply the right scale quotient upper bound
-- statement:
--   For the actual killed discounted first-record grid weights of a spectrally negative Lévy process, a pathwise upper cover of the stopped Stieltjes dividend reward and a one-step bound on expected record payments with ratio W(a)/W(a+epsilon) imply the exact upper finite-difference quotient for the barrier value. Measurability and geometric iteration follow from proved theorems; only the pathwise cover and stochastic one-step renewal estimate remain explicit.
-- source:
--   Root-connected reduction for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69, importing the proved actual-grid AEMeasurable theorem, geometric expectation recurrence helper, and right scale quotient valuation theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_upper_of_step
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_record_budgets

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_killed_grid_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (a b q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (b + (n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * ε) ω).toReal)))
      else 0)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
    (hstep : ∀ n,
      (∫⁻ ω, w (n + 1) ω ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
          (∫⁻ ω, w n ω ∂P)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
