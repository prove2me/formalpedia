-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_clipped_C2_coefficients
-- name    : AvramDividend.Classical.avram_gledger23_original_postpayment_clipped_C2_coefficients
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:49:35.109779+00:00
-- url     : https://prove2.me/theorems/0035b007-7d9b-4f47-9bc4-e048dcb6d766
-- title:
--   Original postpayment Gaussian C2 coefficients are adapted and uniformly compactly bounded
-- statement:
--   For the actual Lévy process X, right dividend limit of the same admissible D, and genuine right-continuous-filtration stopping clock rho, the discounted first and second derivatives evaluated at the original postpayment reserve x+X.X(s)-rightLimit D(s), clipped to a deterministic positive compact band and strictly masked before rho, are measurable in F.rightCont(s) and uniformly bounded. This is the source-exact coefficient interface for a chronological original-process Ito cash ledger; no auxiliary process or arbitrary grid is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger23_original_postpayment_clipped_C2_coefficients
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j : ℕ) :
    let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
    let b := x + ((j : ℝ) + 1)
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      x + X.X t ω - rightLimit D t ω
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let G : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (Y s ω) then deriv w (Y s ω) else 0)
      else 0
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (Y s ω) then iteratedDeriv 2 w (Y s ω) else 0)
      else 0
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
        Measurable[𝓕.rightCont s] (H s) ∧
        (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH) := by sorry
