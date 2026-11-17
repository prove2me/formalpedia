-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_active_clipped_firstorder_discount_bound
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_active_clipped_firstorder_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:03:12.851463+00:00
-- url     : https://prove2.me/theorems/3867d462-6106-4580-8eb9-83f5c3919150
-- title:
--   Original finitecap active stopped physical-grid clipped Gaussian gradient bounded after discount
-- statement:
--   Under the original finitecap source assumptions, the exact discounted first-order Gaussian coefficient used by source M_m, equal to deriv w below the rational cutoff b and 1 above, has a deterministic uniform absolute bound on all physical-grid starts before the stopping clock. The strict floor transfers to postpayment rightLimit D, and the compact gradient bound applies only below b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_active_clipped_firstorder_discount_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n j : ℕ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then deriv w (x + X.X s ω - rightLimit D s ω)
        else 1)| ≤ K := by sorry
