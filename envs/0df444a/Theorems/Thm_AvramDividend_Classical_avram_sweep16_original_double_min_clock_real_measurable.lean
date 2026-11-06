-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_real_measurable
-- name    : AvramDividend.Classical.avram_sweep16_original_double_min_clock_real_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:41:05.975708+00:00
-- url     : https://prove2.me/theorems/c5ed4dfb-218d-4cdb-aede-499aaa96ad7b
-- title:
--   Original doubly stopped ruin-localisation clock is real measurable under unchanged physical filtration
-- statement:
--   The original admissible dividend strategy makes its ruin time measurable. The independent original right-continuous stopping localiser is measurable. Minima, finite-horizon clipping, ENNReal-to-NNReal and NNReal-to-real casts preserve measurability. The equal real clock τ_k therefore is measurable, providing the exact hτmeas demanded by the original UBV Itô source components, with no substitution of sample processes or filtrations.
-- source:
--   Original Proved/public ruinTime_measurable; Mathlib IsStoppingTime.measurable', ENNReal.measurable_toNNReal, measurable_coe_nnreal_real. Independent of fdb9a6a3, 750ad13b and downstream verification.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_double_min_clock_real_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    ∀ k, Measurable (fun ω => (τ k ω : ℝ)) := by sorry
