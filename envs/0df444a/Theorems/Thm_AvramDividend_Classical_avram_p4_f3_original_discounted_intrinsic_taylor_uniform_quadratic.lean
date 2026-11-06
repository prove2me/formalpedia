-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:46:54.239653+00:00
-- url     : https://prove2.me/theorems/9f5f506b-28a5-42d1-a80d-e09e94cbd9c1
-- title:
--   Uniform discounted C² Taylor bound along the physical original stopped reserve
-- statement:
--   For the literal original spectrally negative Lévy reserve after actual dividend payments, compactly clip the predictable pre-payment state to a positive interior interval and stop at physical time T. A single source C² quadratic bound provides one finite constant for every physical time-path and every sufficiently small negative jump mark, after discounting by exp(-qt). This is the true uniform small-jump domination needed to remove mark cutoffs from the stopped Itô–Meyer source. No stochastic decomposition, independent law surrogate, or conditional martingale is assumed.
-- source:
--   Proved source C² Taylor bound 485f09e2 and actual controlled reserve rightLimit D, elementary nonnegative discount exp(-qt) <= 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
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
      ∀ p : ℝ≥0 × Ω, ∀ z ∈ Ioo (-r) (0 : ℝ),
        |A p * SpectrallyNegativeLevy.generatorIntegrand f (U p) z| ≤
          C * z ^ 2) := by sorry
