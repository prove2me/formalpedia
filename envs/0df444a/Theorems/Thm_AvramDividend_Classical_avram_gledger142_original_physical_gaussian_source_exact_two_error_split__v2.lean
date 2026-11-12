-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
-- name    : AvramDividend.Classical.avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:33:49.504566+00:00
-- url     : https://prove2.me/theorems/72acc612-f305-40bb-9e12-2aa529fdc563
-- title:
--   Original stopped Gaussian physical residual is exactly time Euler plus spatial Taylor errors
-- statement:
--   The original postpayment stopped Gaussian finite-mesh residual S-M-G is pointwise exactly the sum A+B of its discounted-clock Euler component and source-specific spatial compensated Taylor component, with all clipped cells, centered Gaussian increments, and original generator accounted for.
-- source:
--   Pointwise physical source identity. Splitting the generator term into the source generator contribution and q times the value reduces the result to finite-sum distributivity and ring algebra. Supports the gledger50 reduction through two strictly smaller absolute L1 limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (ρ : Ω → ℝ≥0)
    (m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let a : ℕ → ℝ := fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i))
    let b : ℕ → ℝ := fun i =>
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))
    let u : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        E s * (deriv w (Y s) * z +
          (iteratedDeriv 2 w (Y s) / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    let g : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0
    let h : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    (Finset.sum (Finset.range (m + 1)) (fun i => a i + b i)) -
      (Finset.sum (Finset.range m) u) -
      (Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * E s * (X.generator w (Y s) - q * w (Y s))
        else 0)) =
      ((Finset.sum (Finset.range (m + 1)) a) +
        (Finset.sum (Finset.range m) h)) +
      ((Finset.sum (Finset.range (m + 1)) b) -
        (Finset.sum (Finset.range m) u) -
        (Finset.sum (Finset.range m) g)) := by sorry
