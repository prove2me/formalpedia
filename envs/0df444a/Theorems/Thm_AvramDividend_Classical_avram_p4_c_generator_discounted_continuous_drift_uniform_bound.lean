-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_continuous_drift_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_continuous_drift_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:21:22.372116+00:00
-- url     : https://prove2.me/theorems/37be2bbf-b47a-4231-8d0b-0e39df2fdaf2
-- title:
--   Uniform source-original discounted Gaussian and epsilon-physical Levy drift bound on compact interior
-- statement:
--   The exact Gaussian second-order generator correction and epsilon-renormalised original physical drift admit a single deterministic nonnegative uniform absolute bound after nonnegative-rate discount at every nonnegative time and reserve in a compact C2 interior band. Derives from source Gaussian compact bound and original finite-annulus Levy drift bound; includes the true c minus negative-annulus first moment and avoids pathwise martingale or endpoint assumptions. This pointwise bound gives a dominated-convergence envelope independent of the stopped clock.
-- source:
--   Source Gaussian compact bound fce33e7b-de46-4ff0-aeda-ad74bd21b08a and original Levy compact physical drift bound 36c9748f-402f-4058-81c1-32e098911d4d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_physical_drift_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_continuous_drift_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q C u v ε : ℝ) (Cap : ℝ≥0∞)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hwCap : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap})
    (hu : 0 < u) (hv : v < C)
    (hBand : Icc u v ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Cap}) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc u v →
      |Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
         (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y)| ≤ M := by sorry
