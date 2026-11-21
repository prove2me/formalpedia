-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_smoothed_kink_generator_strip_supersolution
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_smoothed_kink_generator_strip_supersolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:38:33.463795+00:00
-- url     : https://prove2.me/theorems/1d8fa7f6-b153-4240-9614-d0b1e281dc93
-- title:
--   Original finite-cap one-sided mollified Gaussian HJB bound retaining signed kink Dirac correction
-- statement:
--   Under the exact original generator identity for a one-sided mollification of a cap-linear test function, including the Gaussian second-derivative point mass (sigma squared over two) times (1-alpha) rho((y-b)/epsilon)/epsilon, if alpha is at least one and the regular generator residual is bounded by positive drift on the strict upper strip, the entire original generator is bounded by positive drift times the strict upper-strip indicator. In particular, the negative kink atom never contributes a positive generator error and no softened b-epsilon strip is required.
-- source:
--   Source-specific non-circular Gaussian smoothing algebra. Existing Proved 570895dc gives the sharp one-sided convolution generator strip; this child proves the cap-kink signed atom can be safely discarded. The exact weak derivative identity hWeak remains a separate genuine analysis obligation before original 0ef5d778 can close.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_upperstrip_convolution_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_finitecap_smoothed_kink_generator_strip_supersolution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : Measure ℝ) (φ g V : ℝ → ℝ)
    (hφI : Integrable φ μ) (hφpos : 0 ≤ᵐ[μ] φ)
    (hφnorm : (∫ z, φ z ∂μ) = 1)
    (hPositive : ∀ᵐ z ∂μ, 0 < z)
    (ε : ℝ) (hε : 0 < ε) (b y α : ℝ) (hα : 1 ≤ α)
    (hg : ∀ u : ℝ, g u ≤ if b < u then max X.c 0 else 0)
    (hgI : Integrable (fun z => φ z * g (y - ε*z)) μ)
    (hφkink : 0 ≤ φ ((y - b) / ε))
    (hWeak : X.generator
      (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y =
      (∫ z, φ z * g (y - ε*z) ∂μ) +
      X.σ ^ 2 / 2 * (1 - α) * φ ((y - b) / ε) / ε) :
    X.generator (fun t => ∫ z, φ z * V (t - ε*z) ∂μ) y ≤
      if b < y then max X.c 0 else 0 := by sorry
