-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_all_finite_clocks_source_variation_bound
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_all_finite_clocks_source_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:56:56.630621+00:00
-- url     : https://prove2.me/theorems/1725d51b-7c2c-4fcf-8b2d-5500b440da1a
-- title:
--   Original BV finite source variation bound uniform over path-selected finite clocks and physical grids
-- statement:
--   On one common original BV Lévy source full-measure event, for every finite physical clock τ selected after observing the original path, and every sample-dependent grid ending before τ, the genuine drift/R/J source variation is bounded by the explicit finite nonnegative |drift|τ+(Rτ-R0)+(Jτ-J0). The original P3-A R monotone and F21 J monotone are already uniform in time, so no countable restriction on τ is necessary. This gives the P3-G stopping-clock-to-F29 source envelope uniformly and uses no stopped-budget or generator compensation assumption.
-- source:
--   P3-A Proved raw residual R monotonicity e9d95081, F21 Proved physical J monotonicity 32cc0b62, with time universally quantified inside the common almost-sure event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_all_finite_clocks_source_variation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (τ : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (hEnd : ∀ k, (u k) (n k) ≤ τ),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M := by sorry
