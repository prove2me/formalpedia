-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_masked_kink_positivepart_upper
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_physical_masked_kink_positivepart_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:09:27.153208+00:00
-- url     : https://prove2.me/theorems/a781e5de-2be1-4218-9bb6-d7b252c03012
-- title:
--   Original finitecap masked positive kink residual dominated by tangent-matched extension source
-- statement:
--   For the original finitecap rational corner b and α=deriv w b≥1, the positive part of the stopped physical-grid caplinear slope-one kink source is bounded by the positive part for the smooth tangent-matched slope α extension, with exactly the original s_i<rho stopping mask, rightLimit D postpayment reserve and weighted Gaussian raw increments. This makes the downward local-time correction favorable rather than requiring its absolute value to vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_physical_masked_kink_positivepart_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (δ q x : ℝ) (j : ℕ)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let α : ℝ := deriv w b
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let g : ℕ → ℝ := fun i => if a ≤ Y i then deriv w (Y i) else 1
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (V (Y i + R i) - V (Y i) -
          (if Y i ≤ b then g i else 1) * R i)
      else 0)) 0 ≤
      max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (U (Y i + R i) - U (Y i) -
          (if Y i ≤ b then g i else α) * R i)
      else 0)) 0  := by sorry
