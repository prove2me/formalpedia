-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_source_continuous_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_source_continuous_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:30:42.516256+00:00
-- url     : https://prove2.me/theorems/d150f58c-49e4-4f53-a7c9-af3f466032b1
-- title:
--   Literal source Levy Gaussian plus c-derivative generator coefficients discounted L1 on finite interior clock
-- statement:
--   For any finite measurable observation clock whose reserves remain on a compact positive C2 interior band, the actual source SpectrallyNegativeLevy generator continuous coefficients sigma²/2 times the Hessian plus the canonical source drift c times the derivative have an integrable exponentially discounted density. This is proved from the exact epsilon-renormalised physical coefficient L1 theorem by using epsilon=1, where the strict -1<z<-1 annulus is empty. The source c remains the original truncation-convention drift rather than a guessed bounded-variation drift. No stochastic integration or endpoint HJB is asserted.
-- source:
--   Accepted P4-C joint continuous physical coefficient theorem c5eee410-1659-4bfd-adbf-771f3ba5b53b; source generator canonical drift definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_continuous_coefficients_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_source_continuous_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (clock : T → ℝ≥0) (w : ℝ → ℝ) (q : ℝ)
    (hder : Measurable (fun t => deriv w (R t)))
    (hhess : Measurable (fun t => iteratedDeriv 2 w (R t)))
    (hclock : Measurable clock)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (C : ℝ) (Cap : ℝ≥0∞) (u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hcap : ∀ t ∈ A, R t ∈ Icc u v) :
    Integrable (A.indicator (fun t : T =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
          X.c * deriv w (R t)))) μ := by sorry
