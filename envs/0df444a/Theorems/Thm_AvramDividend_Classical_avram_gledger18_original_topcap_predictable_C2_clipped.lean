-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_predictable_C2_clipped
-- name    : AvramDividend.Classical.avram_gledger18_original_topcap_predictable_C2_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:33:33.511205+00:00
-- url     : https://prove2.me/theorems/cc410911-1b51-4765-9a69-24034676cc04
-- title:
--   Original stopped Gaussian C2 coefficients are predictable and bounded on compact bands
-- statement:
--   The original adapted dividend-controlled surplus, sampled at a deterministic time and masked before the original right-continuous stopping time, gives right-continuous-filtration measurable C2 gradient and Hessian coefficients after clipping to the strictly positive compact surplus band. Both discounted coefficients are globally bounded, using the source Gaussian compact C2 envelope. This supplies the missing actual-coefficient hypotheses for the ad7f605e physical Gaussian centred grid; it does not assume a false global derivative bound or an independent Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger18_original_topcap_predictable_C2_clipped
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
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let G : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (riskProcess X x D s ω) then
            deriv w (riskProcess X x D s ω) else 0)
      else 0
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (riskProcess X x D s ω) then
            iteratedDeriv 2 w (riskProcess X x D s ω) else 0)
      else 0
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
        Measurable[𝓕.rightCont s] (H s) ∧
        (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH) := by sorry
