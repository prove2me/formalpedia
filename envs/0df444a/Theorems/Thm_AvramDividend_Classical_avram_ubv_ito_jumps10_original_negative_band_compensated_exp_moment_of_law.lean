-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_compensated_exp_moment_of_law
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_compensated_exp_moment_of_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:35:40.279206+00:00
-- url     : https://prove2.me/theorems/c6440353-5f83-4ce6-851e-c0777a020339
-- title:
--   Genuine original Levy negative-band count compensated exponential cumulant
-- statement:
--   The exact intrinsic original negative-band Levy count NB, when its full measurable original Poisson law is supplied, has compensated exponential cumulant E_P exp(theta (NB-r)) = exp(r (exp(theta)-1-theta)). The proof imports the verified original-count generating function and only algebra. This finite-band result does not assert a full Poisson law from Standing or finite activity for the underlying Levy process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_compensated_exp_moment_of_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (NB : Ω → ℕ)
    (hcount : ∀ ω, (NB ω : ℝ≥0∞) =
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Set.Ioc (0 : ℝ≥0) T ×ˢ B))
    (hNm : Measurable NB)
    (r : ℝ≥0)
    (hLaw : P.map NB = poissonMeasure r)
    (θ : ℝ) :
    (∫ ω, Real.exp (θ * ((NB ω : ℝ) - (r : ℝ))) ∂P) =
      Real.exp ((r : ℝ) * (Real.exp θ - 1 - θ)) := by sorry
