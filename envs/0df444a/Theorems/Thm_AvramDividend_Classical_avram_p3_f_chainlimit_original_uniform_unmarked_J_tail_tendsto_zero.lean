-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:27:33.840201+00:00
-- url     : https://prove2.me/theorems/7ae15431-c28f-49ca-867d-3696e27f287b
-- title:
--   Actual original BV unmarked jump-cell mass tends to zero under finite-source tail exhaustion
-- statement:
--   For the genuine original BV Levy jump accumulator, on one full-measure event uniform over path-dependent finite negative jump sets, any deterministic right-closed grid sequence that isolates the selected marks and whose actual remaining finite-source J mass tends to zero admits a physical tag sequence with unmarked J-cell mass tending to zero. This connects the accepted uniform original finite-mark envelope to the actual source-tail limit, without assuming the stopped chain inequality or generator compensation.
-- source:
--   Accepted F26 uniform unmarked physical J exclusion 41c6650f, F21 actual monotone original J 32cc0b62 and the pinned real squeeze theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_unmarked_J_tail_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ k i, i < n k → (u k) i ≤ (u k) (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      ∀ (T : ℕ → Finset ℝ≥0)
        (hCover : ∀ k, ∀ v ∈ T k, ∃ i : ℕ,
          i < n k ∧ (u k) i < v ∧ v ≤ (u k) (i + 1))
        (hSeparate : ∀ k, ∀ v ∈ T k, ∀ z ∈ T k, ∀ i : ℕ,
          i < n k → (u k) i < v → v ≤ (u k) (i + 1) →
          (u k) i < z → z ≤ (u k) (i + 1) → v = z),
        Tendsto (fun k =>
          J ((u k) (n k)) - J ((u k) 0) -
            (T k).sum (fun v =>
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω))
          atTop (nhds 0) →
        ∃ tag : ℕ → ℝ≥0 → ℕ,
          (∀ k, ∀ v ∈ T k,
            tag k v < n k ∧ (u k) (tag k v) < v ∧
              v ≤ (u k) (tag k v + 1)) ∧
          (∀ k, ∀ v ∈ T k, ∀ z ∈ T k,
            tag k v = tag k z → v = z) ∧
          Tendsto (fun k =>
            (Finset.range (n k)).sum (fun i =>
              if i ∈ (T k).image (tag k) then 0
              else J ((u k) (i + 1)) - J ((u k) i)))
            atTop (nhds 0) := by sorry
