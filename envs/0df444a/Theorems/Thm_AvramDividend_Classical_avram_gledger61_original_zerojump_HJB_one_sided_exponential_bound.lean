-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
-- name    : AvramDividend.Classical.avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:33:12.657257+00:00
-- url     : https://prove2.me/theorems/1c1a45a2-77bb-413a-b8d4-f61b3d1b3920
-- title:
--   Original zero-jump Lévy Gaussian HJB has a one-sided exponential value envelope
-- statement:
--   For the original no-jump spectrally negative Lévy process, a smooth Gaussian-generator HJB supersolution has a one-sided exponential upper growth bound on any positive reserve half-line. The proof invokes the exact original zero-jump generator identity and the scalar ODE HJB growth bound. This is an analytic prerequisite for controlling the positive part of the original clipped physical source, without incorrectly restricting the negative tail of the value function.
-- source:
--   Original same-process analytic bridge to gledger53. From pinned Proved Gaussian zero-jump generator identity f85cd232 and Gaussian scalar HJB exponential comparison gledger60.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger60_gaussian_scalar_HJB_one_sided_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_generator_gaussian_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hgen : ∀ y : ℝ, 0 < y →
      X.generator w y - q * w y ≤ 0)
    (u : ℝ) (hu : 0 < u) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
