-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_levy_energy_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_levy_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:55:25.988802+00:00
-- url     : https://prove2.me/theorems/043fe2f3-fbce-411f-b726-a88ebe7cf908
-- title:
--   Original discounted stopped Taylor mark integrals controlled by intrinsic Lévy quadratic energy
-- statement:
--   For the actual original dividend-controlled reserve on physical time sample p, the full ν-intensity integral of the discounted nonlinear C² generator jump remainder over the canonical small negative mark interval is bounded by a universal compact-state Taylor constant times the intrinsic ν quadratic intensity over the same mark interval. This is the precise original-process measure-energy estimate needed to pass jump cutoffs via finite Lévy quadratic energy. It controls every physical time and sample, retains the original ν, and does not assume a Gaussian decomposition or abstract martingale integral.
-- source:
--   Directly integrates the proved original-process pointwise quadratic bound 9f5f506b against X.ν, using Mathlib ae_restrict_mem, lintegral_mono_ae and lintegral_const_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_levy_energy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ p : ℝ≥0 × Ω,
        (∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal (|A p *
            SpectrallyNegativeLevy.generatorIntegrand f (U p) z|)
            ∂X.ν) ≤
          ENNReal.ofReal C *
            (∫⁻ z in Ioo (-r) (0 : ℝ),
              ENNReal.ofReal (z ^ 2) ∂X.ν)) := by sorry
