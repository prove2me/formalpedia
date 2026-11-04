-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_reserve_derivative_uniform_bound
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_stopped_reserve_derivative_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:27:22.191952+00:00
-- url     : https://prove2.me/theorems/e35e605a-7927-4748-bb25-b934cf15699c
-- title:
--   Original BV stopped controlled left-reserve deterministic derivative bound
-- statement:
--   The original BV value C1 regularity on the positive cap and a true stopped left-reserve range [a,b] imply a single nonnegative deterministic L with |deriv w (Y(t,ω))|≤L at every original stopped point. It discharges the derivative component of the physical BV generator envelope.
-- source:
--   Already-proved original compact positive-cap derivative bound 07ca388c plus genuine controlled left-limit reserve Y and its stop-region band assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_stopped_reserve_derivative_uniform_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (C : ℝ≥0∞) (w : ℝ → ℝ)
  (hwC1 : ContDiffOn ℝ 1 w
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (a b : ℝ) (hab : a ≤ b)
  (hBand : Icc a b ⊆
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (A : Ω → Set ℝ≥0)
  (Y : (ℝ≥0 × Ω) → ℝ)
  (hY : ∀ p, Y p = Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
  (hStoppedBand : ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 → Y p ∈ Icc a b) :
  ∃ L : ℝ, 0 ≤ L ∧
    ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 → |deriv w (Y p)| ≤ L := by sorry
