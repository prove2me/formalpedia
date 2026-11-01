-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2
-- name    : AvramDividend.Classical.avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:51:04.718197+00:00
-- url     : https://prove2.me/theorems/08dd89a3-95ba-4597-a20b-42eb2a7cab35
-- title:
--   Controlled pre-jump gradient square integrable against genuine finite-horizon Lebesgue time and original probability
-- statement:
--   For the original adapted spectrally negative Lévy source and arbitrary admissible dividend strategy, a value function smooth only on a strict interior interval yields a predictable compact-band controlled pre-jump gradient whose squared magnitude is integrable directly with respect to the genuine real Lebesgue horizon time × original probability P, not merely an abstract finite predictable observation measure. This is the exact analytic Brownian-integrand energy prerequisite and does not assert existence of a Brownian component or a stochastic integral.
-- source:
--   Proved cd6/168 finite-horizon predictable all-lintegral equality on actual time×P and bcd controlled compact gradient L² energy, pinned Mathlib Measurable.ennreal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] G ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2)
        ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤ := by
  sorry
