-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone
-- name    : AvramDividend.Classical.avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:50:26.54621+00:00
-- url     : https://prove2.me/theorems/31bcca2b-9c2e-4494-a223-83dd35a162a9
-- title:
--   Original source positive-interior nested bounded exit clocks are stopping times and increase under band/horizon widening
-- statement:
--   For the original controlled post-payment reserve x + X.X s ω - rightLimit D s ω with the exact ContDiffOn ℝ 2 positive reserve domain, take two finite closed interior bands [lower1,upper1] contained in [lower2,upper2], and two finite time horizons B1≤B2. The original dense-grid first-exit clocks stopped at B1 and B2 are each stopping times for the original filtration's right-continuous modification, by the previously Proved source-specific stopping and C² theorem. The first is pointwise no later than the second, since exiting the wider band implies exiting the narrower band at the same grid point and min/inf preserve order. This supplies a genuine monotonicity component for a later exhaustion theorem but does not claim convergence to the ruin/cap clock or predictability of a strict pre-exit mask.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0)
    (lower₁ upper₁ lower₂ upper₂ : ℝ)
    (hlower₁ : 0 < lower₁) (hlower₂ : 0 < lower₂)
    (hlo : lower₂ ≤ lower₁) (hup : upper₁ ≤ upper₂)
    (hcap₁ : ∀ y ∈ Set.Icc lower₁ upper₁, ENNReal.ofReal y < C)
    (hcap₂ : ∀ y ∈ Set.Icc lower₂ upper₂, ENNReal.ofReal y < C)
    (hdense : DenseRange r)
    (B₁ B₂ : ℝ≥0) (hB : B₁ ≤ B₂) :
    let τ₁ : Ω → WithTop ℝ≥0 := fun ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
            upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B₁ : WithTop ℝ≥0)
    let τ₂ : Ω → WithTop ℝ≥0 := fun ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower₂ ∨
            upper₂ < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B₂ : WithTop ℝ≥0)
    IsStoppingTime 𝓕.rightCont τ₁ ∧
      IsStoppingTime 𝓕.rightCont τ₂ ∧
      ∀ ω, τ₁ ω ≤ τ₂ ω := by sorry
