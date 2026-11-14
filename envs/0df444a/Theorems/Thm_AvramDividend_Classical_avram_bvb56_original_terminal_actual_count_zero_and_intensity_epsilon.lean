-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
-- name    : AvramDividend.Classical.avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:28:35.923327+00:00
-- url     : https://prove2.me/theorems/d90f8bb6-0849-4680-886a-77f3255433be
-- title:
--   Finite-activity original terminal-strip joint actual mark exclusion and predictable intensity epsilon certificate
-- statement:
--   For each prescribed finite-activity original BV source and every strictly positive epsilon, on a single original P-conull event, all sufficiently late exact original uniform final physical cells simultaneously carry zero actual negative jumps and have predictable negative Levy intensity mass below epsilon. Both statements retain the original same physical horizon T, source filtration and count measure. This provides the joint almost-sure/deterministic terminal-strip certificate needed when estimating the uncompensated final physical mesh in the BVB49 survivor and ruin Stieltjes cash obligations.
-- source:
--   Previously Proved original source last-strip counting theorem BVB51 and finite negative Levy compensator-rate terminal width theorem BVB52.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 ∧
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2)) < ε := by sorry
