-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB59_original_finitecap_postpayment_gradient_grid_filtered
-- name    : AvramDividend.Classical.avram_gbB59_original_finitecap_postpayment_gradient_grid_filtered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:11:38.360198+00:00
-- url     : https://prove2.me/theorems/26d4a3ab-445e-44d0-b6c2-afa2f3f4922e
-- title:
--   Adaptedness of the original finite-cap postpayment clipped-gradient Gaussian grid coefficient
-- statement:
--   At every deterministic finite-cap Gaussian grid time, the original stopped postpayment clipped-gradient coefficient is measurable with respect to the original right-continuous filtration at that same time. This gives the predictable coefficient condition required for original Gaussian two-grid isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB59_original_finitecap_postpayment_gradient_grid_filtered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
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
    ∀ (m i : ℕ),
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))]
        (G m i) := by sorry
