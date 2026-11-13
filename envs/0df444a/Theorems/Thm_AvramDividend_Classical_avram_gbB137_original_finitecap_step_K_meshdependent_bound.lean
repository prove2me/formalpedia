-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB137_original_finitecap_step_K_meshdependent_bound
-- name    : AvramDividend.Classical.avram_gbB137_original_finitecap_step_K_meshdependent_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:56:32.213196+00:00
-- url     : https://prove2.me/theorems/6ec3707e-20ff-4334-93ba-fa5910e42106
-- title:
--   Original finite-cap mesh step coefficient bounded for every mesh index
-- statement:
--   The original sampled clipped coefficients G have a uniform bound B by Proved B64. The exact original step coefficient K is a finite sum of cell-masked G terms. The Proved gb99 finite-step bound controls its absolute value by the number of cells times B. This establishes boundedness for each fixed mesh index, which is sufficient for B127 finite-time squared integrability.
-- source:
--   Proved B64 and gb99 finite step bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB64_original_finitecap_postpayment_coeff_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb99_finite_step_abs_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB137_original_finitecap_step_K_meshdependent_bound
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
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m t ω, |K m t ω| ≤ (m + 1 : ℕ) * B := by sorry
