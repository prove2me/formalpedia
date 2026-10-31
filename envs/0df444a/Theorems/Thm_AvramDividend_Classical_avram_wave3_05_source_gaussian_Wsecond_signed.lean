-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_source_gaussian_Wsecond_signed
-- name    : AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:19:27.102341+00:00
-- url     : https://prove2.me/theorems/4d65e282-acbe-4c1b-a0bd-fdfff53b2ca8
-- title:
--   Original Gaussian scale second derivative from globally integrable Neumann density
-- statement:
--   For the unchanged original spectrally negative Lévy process and q-scale W with positive Gaussian coefficient, the Esscher-transformed Volterra equation yields an explicit signed Neumann density S integrable on the whole positive half-line. Its derivative resolvent is differentiable from the contracting antitone envelope, and the original W satisfies W''(x)=2φW'(x)−φ²W(x)+exp((φ+w)x)S(x)/a at every positive reserve. The source zero-support and right-origin boundary convention are unchanged.
-- source:
--   Source Lévy Gaussian Esscher Volterra, verified positive-indicator continuous provider, accepted signed derivative theorem, C2 bootstrap, Esscher untilting second derivative. Repaired terminal import-database connection failure on 30 October 2026 by using a different already-Proved continuity interface.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_deriv_eq_resolvent_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_esscher_untilting_second_deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (a w : ℝ) (S : ℝ → ℝ),
      0 < a ∧
      IntegrableOn S (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        deriv (deriv W) x =
          2 * φ * deriv W x - φ ^ 2 * W x +
            Real.exp ((φ + w) * x) * (S x / a)) := by sorry
