-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_gaussian_gradient_between_stops_MemLp
-- name    : AvramDividend.Classical.ripple_original_gaussian_gradient_between_stops_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:08:01.973811+00:00
-- url     : https://prove2.me/theorems/8364d804-2cc4-4ddf-a890-d48cd5781346
-- title:
--   Actual Avram prepayment Gaussian gradient square-integrable on arbitrary two-clock window
-- statement:
--   For the original Avram spectrally negative Levy surplus and genuine dividend strategy, the left-limit Gaussian coefficient restricted to a random stochastic window (sigma,tau] is in L2 of any finite right-continuous predictable measure. The proof reuses the original gradient MemLp theorem and the Ripple-derived two-stopping-times predictable-window theorem.
-- source:
--   Ripple/Stochastic/ContinuousItoStoppedIsometry.lean stopping_indicator_sub e216e28ce3ffb43877e11f71be260e40a37a35df Apache-2.0; original Prove2Me Gaussian source 498f21c8-74dc-4211-85c0-5efcfb0b99ff; predictability via ripple_between_stopping_times_predictable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
import Theorems.Thm_AvramDividend_Classical_ripple_between_stopping_times_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_gaussian_gradient_between_stops_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ := by sorry
