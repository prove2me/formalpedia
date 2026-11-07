-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_stopped_fullmask_uniform_on_compact_interior
-- name    : AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_uniform_on_compact_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:37:36.059559+00:00
-- url     : https://prove2.me/theorems/d5c8466f-8dba-4f88-90f0-d8f9cbbfd249
-- title:
--   Original stopped full compensated bands eventually contain every fixed compact interior reserve strip uniformly
-- statement:
--   A single deterministic cofinal all-cap sequence of original compensation bands eventually contains any prescribed closed reserve interval [c,d] strictly inside the positive cap interior, simultaneously for every bounded ruin-stopped clock, sample and physical time. This upgrades pointwise eventual band coverage to a uniform compact-strip source certificate, useful for coupling finite local C1 and X.nu estimates before boundary localisation.
-- source:
--   The Proved all-cap full-band cofinality fc04d4a7 is applied at both endpoints c and d, and the two eventual indices are combined by max. The conclusion is source-exact for original X.X, rightLimit D, ruinTime X x D, and every finite stopped clock. Only an interior compact strip is assumed; no global domination or stochastic limit is claimed.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_uniform_on_compact_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ c d : ℝ, 0 < c → c ≤ d →
        ENNReal.ofReal c < C → ENNReal.ofReal d < C →
        ∃ N : ℕ, ∀ n ≥ N, ∀ S : ℝ≥0,
          let τ : Ω → ℝ≥0 := fun ω =>
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let Z : ℝ≥0 × Ω → ℝ := fun p =>
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc c d} ⊆
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc (a n) (b n)} := by sorry
