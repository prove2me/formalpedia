-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_two_clock_gaussian_stopped_progressive_L2
-- name    : AvramDividend.Classical.ripple_original_two_clock_gaussian_stopped_progressive_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:40:45.264334+00:00
-- url     : https://prove2.me/theorems/47672d6d-ac6e-4855-8dc1-63a77d3ba34e
-- title:
--   Actual original Gaussian left-limit prepayment coefficient between physical stopping times: strongly progressive and finite physical-time L2
-- statement:
--   For the exact original spectrally negative Levy surplus and an adapted left-continuous dividend strategy, the Gaussian stochastic-integral coefficient from the genuine left-limit prepayment reserve, masked to a compact interior band and a random physical-time interval (sigma,tau], is strongly progressively measurable for the original right-continuous filtration. It is L2 under a finite measure agreeing with actual finite-horizon physical time times original probability on predictable events. This is a joint physical stochastic-integral input certificate and makes no unsupported Ito cash or martingale representation claim.
-- source:
--   Proved original Gaussian predictability 7ae1130d-7935-43f5-ad75-a3ce3d5de9ac, true physical time MemLp d09cd104-573e-43b2-8a18-62b99fbf8a09, Ripple two stopping predictable interval 730ba1ff-2b25-4037-8d77-beff6f5f8483, Mathlib strongly predictable to strongly progressive. Ripple stopped-isometry source commit e216e28ce3ffb43877e11f71be260e40a37a35df Apache-2.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ripple_between_stopping_times_predictable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_ripple_original_physical_time_two_clock_Gaussian_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_two_clock_gaussian_stopped_progressive_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      IsStronglyProgressive 𝓕.rightCont
        (fun t ω => S.indicator G (t,ω)) ∧
      MemLp (S.indicator G) 2 μ := by sorry
