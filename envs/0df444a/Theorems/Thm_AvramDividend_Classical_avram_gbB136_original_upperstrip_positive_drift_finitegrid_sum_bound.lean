-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB136_original_upperstrip_positive_drift_finitegrid_sum_bound
-- name    : AvramDividend.Classical.avram_gbB136_original_upperstrip_positive_drift_finitegrid_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:46:07.407276+00:00
-- url     : https://prove2.me/theorems/776a7faa-c601-4ae0-8590-4860497f29b1
-- title:
--   Original physical upper-strip caplinear drift correction sums with the necessary positive-drift charge
-- statement:
--   Sum the Proved original upper-strip B68 discounted physical-grid cell estimate over every genuine upper-strip cell where both prepayment and postpayment reserves exceed the fixed band cutoff. The total surplus of the caplinear spatial increment above the centred Gaussian noise is at most max(c,0) times the sum of discounted physical cell widths on that upper strip. This records the positive-drift occupation charge missing from the disputed original fixed-band cash theorem 69952618, preserving exact original Y/Z/right-limit dividend conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB136_original_upperstrip_positive_drift_finitegrid_sum_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if b < Y i ∧ b < Z i then
        e i * (Δ : ℝ) * max X.c 0 else 0) := by sorry
