-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb44_original_finitecap_predictable_H_measurable_uniform_bound
-- name    : AvramDividend.Classical.avram_gb44_original_finitecap_predictable_H_measurable_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:37:39.416197+00:00
-- url     : https://prove2.me/theorems/9c3ebb13-11aa-4e06-81ac-a347eaa6df32
-- title:
--   Original finite-cap stopped Hessian grid coefficients are measurable and uniformly bounded
-- statement:
--   For the original zero-jump finite-cap dividend strategy, a fixed interior compact interval and stopped right-continuous filtration, the postpayment deterministic-grid Hessian coefficients H_i are measurable on the original probability space. A common nonnegative bound controls their absolute values uniformly over all grid sizes and cell indices. The bound follows from compact C2 regularity, positive discounting and predictable measurability of the original reserve, without an auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb44_original_finitecap_predictable_H_measurable_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then iteratedDeriv 2 w Y else 0)
      else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i,
      Measurable (H m i) ∧ ∀ ω, |H m i ω| ≤ B := by
  sorry
