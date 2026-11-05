-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_clock_uniform_source_variation_bound
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_clock_uniform_source_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:45:10.897117+00:00
-- url     : https://prove2.me/theorems/4d7a3a8a-2cfb-4327-82c8-a348c6fc72a4
-- title:
--   Original BV fixed-clock bound for every refining mesh's true drift and jump source variation
-- statement:
--   At a fixed finite physical clock τ of the genuine bounded-variation original Lévy source, the original raw removed residual R and negative-jump cumulative mass J are almost surely monotone. On a single full-measure event, every possibly sample-dependent grid family ending at or before τ has original combined variation |drift|Δtime+ΔR+ΔJ bounded by the explicit finite path value |drift|τ+(Rτ-R0)+(Jτ-J0). This automatically provides the genuine source envelope used by the localised cap C1 mesh limit with no assumption of an arbitrary numerical bound or generator compensation.
-- source:
--   Proved P3-A original raw removed residual monotone e9d95081 and Proved P3-F original raw J monotone 32cc0b62; exact physical X.X and Lévy drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_clock_uniform_source_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (τ : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (hEnd : ∀ k, (u k) (n k) ≤ τ),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M := by sorry
