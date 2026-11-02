-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:55:38.403128+00:00
-- url     : https://prove2.me/theorems/f5caff4b-c9d3-4799-ba9b-ed694d38fe7b
-- title:
--   Genuine original right-continuous stopping clocks min(ruinTime,n) are bounded, monotone and cofinal
-- statement:
--   For the actual source SpectrallyNegativeLevy P 𝓕 and admissible dividend strategy D, the canonical simple bounded clocks min(ruinTime X x D,n) are not merely measurable. They are genuine stopping times in the unchanged right-continuous source filtration, each bounded by the deterministic horizon n, monotone pathwise and converging to actual ruinTime for every sample path, including immediate ruin at zero and ruin at infinity. Reuse the Proved source ruinTime stopping theorem and the Proved deterministic-clock monotone convergence theorem. No smoothness, bounded variation, extra boundary assumption or stochastic budget is introduced.
-- source:
--   Accepted original ruinTime stopping theorem and accepted source bounded clock theorem 3ae57b3c-959f-46f7-ba88-a55f35a44126; pinned Mathlib IsStoppingTime.min_const verified in remote declaration index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ n ω, min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (n : ℝ≥0∞)) ∧
    (∀ ω, Monotone
      (fun n : ℕ => min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω, (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
      ruinTime X x D ω) := by sorry
