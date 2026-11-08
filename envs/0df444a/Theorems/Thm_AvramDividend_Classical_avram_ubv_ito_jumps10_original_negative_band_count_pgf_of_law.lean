-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:41:26.34154+00:00
-- url     : https://prove2.me/theorems/512cbb9e-d7bc-4472-8eca-b9ef1f41ae30
-- title:
--   Original intrinsic negative-band jump-count exponential moment from its genuine Poisson law
-- statement:
--   For the actual source Lévy process X, let NB count its strictly positive-time jumps with marks in band B up to T. If NB is measurable and its original-space law is Poisson(r), then its real exponential generating function equals exp(r(a-1)). The count law is an explicit independent assumption to be discharged for X; this statement does not construct a substitute process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law
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
    (a : ℝ) :
    (∫ ω, a ^ NB ω ∂P) = Real.exp ((r : ℝ) * (a - 1)) := by sorry
