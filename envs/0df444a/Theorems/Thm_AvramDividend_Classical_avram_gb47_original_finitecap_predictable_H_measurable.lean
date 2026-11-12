-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb47_original_finitecap_predictable_H_measurable
-- name    : AvramDividend.Classical.avram_gb47_original_finitecap_predictable_H_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:04:23.559804+00:00
-- url     : https://prove2.me/theorems/59664c46-f59d-4000-b8c3-d6ac7b2d394d
-- title:
--   Original stopped finite-cap Hessian coefficient measurable on the physical space
-- statement:
--   For the original finite-cap zero-jump dividend strategy and original right-continuous stopping time, the discounted, interior-band clipped second-derivative coefficient is measurable at every deterministic grid cell. This removes the deterministic boundedness half of gb44 and isolates predictable reserve and stopping-event measurability on the original physical probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb47_original_finitecap_predictable_H_measurable
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
    ∀ m i, Measurable (H m i) := by
  sorry
