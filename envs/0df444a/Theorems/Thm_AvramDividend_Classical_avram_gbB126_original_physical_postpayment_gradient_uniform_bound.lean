-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB126_original_physical_postpayment_gradient_uniform_bound
-- name    : AvramDividend.Classical.avram_gbB126_original_physical_postpayment_gradient_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:37:28.764252+00:00
-- url     : https://prove2.me/theorems/3d74ebd6-7783-416e-affa-1ec775af7c22
-- title:
--   Physical-time original finite-cap stopped postpayment clipped gradient is uniformly bounded
-- statement:
--   The original postpayment physical-time clipped gradient (strict stopping at rho, rightLimit D, positive compact clipped interior) is uniformly bounded in sample path and time. A direct specialisation of Proved B60 which provides a bound for arbitrary measurable-space path Y at all nonnegative times. This supplies the physical H bound for B116 dominated convergence and B121 source-specific L2 energies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB126_original_physical_postpayment_gradient_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |H s ω| ≤ B := by sorry
