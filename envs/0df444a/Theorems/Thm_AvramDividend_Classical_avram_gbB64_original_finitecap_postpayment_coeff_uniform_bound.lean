-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_finitecap_postpayment_coeff_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB64_original_finitecap_postpayment_coeff_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:00:39.257831+00:00
-- url     : https://prove2.me/theorems/4d3fb3ef-4eda-4d1f-a980-d778683a6b4c
-- title:
--   Source-exact original Gaussian postpayment coefficient bound directly from compact derivative
-- statement:
--   For the original Gaussian reserve and dividend path, the discounted strict-prestop clipped derivative coefficient on each finite-cap uniform grid is uniformly bounded, using only the proved interior compact derivative bound. This is the graph-stable source coefficient prerequisite for the two-grid Gaussian energy inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB64_original_finitecap_postpayment_coeff_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m i : ℕ) (ω : Ω), |G m i ω| ≤ B := by sorry
