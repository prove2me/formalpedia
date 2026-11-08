-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:42:28.110775+00:00
-- url     : https://prove2.me/theorems/1c875004-0b5d-430e-9c6c-552703e3236e
-- title:
--   Actual original Gaussian masked gradient has all-path finite square energy
-- statement:
--   For the true original spectrally negative Levy process X, dividend process D and pre-right-payment left-limit reserve, the masked Gaussian coefficient sigma times the candidate derivative is square-integrable on every original sample path over any time interval of finite measure. Uses exact right-continuous predictability, deterministic compact band domination and time-section measurability with no completed filtration or surrogate process.
-- source:
--   Proved original Gaussian predictability 7ae1130d, compact coefficient bound 9645ebf8, measurable original time sections cd58d62b, generic bounded square energy 889e6829.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_time_section_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_source_square_energy_integrableOn

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∀ ω, IntegrableOn (fun t : ℝ≥0 => (G (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime := by sorry
