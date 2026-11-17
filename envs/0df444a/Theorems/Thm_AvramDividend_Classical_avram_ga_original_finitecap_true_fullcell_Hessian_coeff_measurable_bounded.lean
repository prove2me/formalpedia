-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:58:21.601269+00:00
-- url     : https://prove2.me/theorems/b363439d-5a7f-4830-a664-db756b5f30f0
-- title:
--   Original stopped finitecap fullcell upperclip Hessian coefficient measurable and uniformly bounded
-- statement:
--   The exact finite-cap Gaussian physical-grid Hessian coefficient with full-cell active mask and only upper clipping at b is measurable and deterministically bounded for all mesh rows and cells. On active cells the proved strict postpayment floor δ makes upper clipping equal to existing gb44 compact [δ/2,b] clipping; gb44 supplies its measurable uniformly bounded coefficient.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

theorem AvramDividend.Classical.avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (if Y ≤ b then iteratedDeriv 2 w Y else 0)
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ m i : ℕ, Measurable (H m i) ∧
        ∀ ω : Ω, |H m i ω| ≤ K := by sorry
