-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb40_original_bounded_hessian_stopped_weight
-- name    : AvramDividend.Classical.avram_gb40_original_bounded_hessian_stopped_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:29:28.526051+00:00
-- url     : https://prove2.me/theorems/cfcef9e4-8ae9-4b59-b61e-669ceb90ac84
-- title:
--   Bounded measurable stopped quadratic Hessian weight under original right-continuous filtration
-- statement:
--   For a zero-jump unbounded-variation Lévy process and a compact interior band, the stopped Hessian coefficient is globally measurable and uniformly bounded, independently of the deterministic grid time, whenever the postpayment reserve argument is adapted at that time.
-- source:
--   Exact original predictable Hessian weight ingredient for gb34 and quadratic grid L2 control, obtained by isolating the coefficient measurability and compact C2 envelope from gb27.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb40_original_bounded_hessian_stopped_weight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∃ KH : ℝ, 0 ≤ KH ∧ ∀ (t : ℝ≥0) (Y : Ω → ℝ),
      Measurable[𝓕.rightCont t] Y →
      let H : Ω → ℝ := fun ω =>
        if t < ρ ω then (1 / 2 : ℝ) *
          Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
        else 0
      Measurable H ∧ ∀ ω, |H ω| ≤ KH := by sorry
