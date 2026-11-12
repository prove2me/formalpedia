-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb50_predictable_stopped_hessian_adapted
-- name    : AvramDividend.Classical.avram_gb50_predictable_stopped_hessian_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:23:54.969801+00:00
-- url     : https://prove2.me/theorems/f17ebdad-7e22-4720-975d-d8924ac457cf
-- title:
--   Original stopped Gaussian Hessian weight is adapted to its deterministic right-continuous time
-- statement:
--   The original stopped Gaussian Hessian coefficient is measurable already in the right-continuous filtration at its deterministic evaluation time, with a uniform bound. This predictable measurability strengthens the proved gb40 coefficient theorem and supplies the later-cell coefficient in original pairwise orthogonality gb33.
-- source:
--   Strengthens gb40 using its original proof's internal hHm subfiltration measurability, retained in the result instead of weakened to global measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb50_predictable_stopped_hessian_adapted
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
      Measurable[𝓕.rightCont t] H ∧ ∀ ω, |H ω| ≤ KH := by sorry
