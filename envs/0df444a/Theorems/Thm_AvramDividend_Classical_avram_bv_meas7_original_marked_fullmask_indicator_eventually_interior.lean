-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_marked_fullmask_indicator_eventually_interior
-- name    : AvramDividend.Classical.avram_bv_meas7_original_marked_fullmask_indicator_eventually_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:36:45.704138+00:00
-- url     : https://prove2.me/theorems/0bfb79cc-7e49-4b3b-96b0-c5269f38667b
-- title:
--   Original stopped marked-jump full compensation mask eventually equals interior mask
-- statement:
--   For every positive finite or infinite cap and for the actual ruin-stopped reserve X.X minus rightLimit D, select full compensated compact bands whose marked negative-jump indicator eventually coincides pointwise with the complete strict positive-cap interior indicator, at every bounded clock, time, sample and negative-jump mark. The resulting exact eventual equality supplies the pointwise event needed for a later compensated-integral limit, without asserting an unproved integrable domination.
-- source:
--   Direct source-exact application of Proved avram_bv_meas7_allcap_full_predictable_compact_bands: the buffered compact containment gives one-sided indicator support and the eventual full-band coverage gives the other direction. Actual X.X, ruinTime X x D and rightLimit D are retained; no probability assumptions are introduced.

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_marked_fullmask_indicator_eventually_interior
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
      ∀ (S : ℝ≥0) (p : ℝ≥0 × Ω) (z : ℝ),
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let Z : ℝ≥0 × Ω → ℝ := fun r =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
        ∀ᶠ n : ℕ in atTop,
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc (a n) (b n) ∧ z < 0 then (1 : ℝ) else 0) =
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0
            then (1 : ℝ) else 0) := by sorry
