-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:39:36.679626+00:00
-- url     : https://prove2.me/theorems/a5de718b-9473-4c3c-b2af-5d8a70148a18
-- title:
--   Original postpayment finite-cap Gaussian first-derivative grid coefficient is measurable and uniformly bounded
-- statement:
--   For every deterministic grid and cell, the stopped, discounted postpayment gradient coefficient with compact interior cutoff is measurable under the original physical law and bounded uniformly in both mesh and cell.
-- source:
--   Sound necessary original X/D gradient measurability and compact C1 bound for original finite-cap Gaussian gbB57, 11 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB58_original_finitecap_predictable_G_measurable_uniform_bound
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i,
      Measurable (G m i) ∧ ∀ ω, |G m i ω| ≤ B := by sorry
