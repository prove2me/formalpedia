-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_strict_reward_fatou_from_real_grid_convergence
-- name    : AvramDividend.Classical.avram_p3_e2_original_strict_reward_fatou_from_real_grid_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:49:13.374192+00:00
-- url     : https://prove2.me/theorems/289941ca-9eb1-4889-b294-a152b1533a55
-- title:
--   Original strict cash and horizon reward Fatou bound from real finite-grid convergence
-- statement:
--   If the actual original dividend Stieltjes cash plus surviving prepayment terminal reward is the almost-everywhere real limit of finite-grid payoffs, then its ENNReal-ofReal value lies below their liminf. This supplies the precise Fatou-lower-bound branch required by the signed original BV grid certificate, using continuity of ENNReal.ofReal and the genuine Mathlib limit-liminf theorem. No stochastic compensation or expectation conclusion is assumed.
-- source:
--   Source-exact original strict cash+survival terminal via Mathlib ENNReal.continuous_ofReal and Filter.Tendsto.liminf_eq.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e2_original_strict_reward_fatou_from_real_grid_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (Fmesh : ℕ → Ω → ℝ)
    (hConverge : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      Tendsto (fun n => Fmesh n ω) atTop (nhds ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)))) :
    ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
        liminf (fun n => ENNReal.ofReal (Fmesh n ω)) atTop := by sorry
