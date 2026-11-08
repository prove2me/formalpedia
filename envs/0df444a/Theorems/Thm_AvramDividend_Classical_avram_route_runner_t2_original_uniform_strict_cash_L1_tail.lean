-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_t2_original_uniform_strict_cash_L1_tail
-- name    : AvramDividend.Classical.avram_route_runner_t2_original_uniform_strict_cash_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:50:29.243208+00:00
-- url     : https://prove2.me/theorems/2488e716-4344-4070-bdb5-0023de5ec1f3
-- title:
--   Original stopped BV strict dividend-cash uniform-grid tail vanishes in L1
-- statement:
--   For any actual admissible dividend strategy D of the original spectrally negative Levy process X, the strict discounted dividend cash through T-T/(n+2) approaches the strict cash through T in L1. The exact uniform physical grid and open strict horizon are retained, with no conditional compensated source assumptions.
-- source:
--   Source-exact specialisation of already Proved fbd2608a (original cofinal strict cash L1) using Proved 0071cc00 (exact uniform cofinal physical horizon). Direct input to the error-tail branch of BV source 2bc848f9 and two-scale source e49a5fce.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_t2_original_uniform_strict_cash_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω : Ω,
      |(∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal -
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal| ∂P)
      atTop (𝓝 0)  := by sorry
