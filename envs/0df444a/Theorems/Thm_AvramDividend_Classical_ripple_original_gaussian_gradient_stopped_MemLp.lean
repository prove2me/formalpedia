-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_gaussian_gradient_stopped_MemLp
-- name    : AvramDividend.Classical.ripple_original_gaussian_gradient_stopped_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:16:47.496479+00:00
-- url     : https://prove2.me/theorems/a734c3a3-289f-4b87-aa35-cc520bd583ba
-- title:
--   Original Avram Gaussian gradient retains L² after a genuine stopped-clock restriction
-- statement:
--   For Avram's original spectrally negative Lévy process and dividend strategy, the actual localised left-limit reserve Gaussian gradient remains L² under an arbitrary stopping-time cut (0,τ] in any finite measure on the right-continuous predictable sigma-algebra. This requires no synthetic stochastic noise or additional Brownian hypothesis.
-- source:
--   Avram Dividend Classical (original model), reusing proved theorem 498f21c8-74dc-4211-85c0-5efcfb0b99ff and Ripple/Stochastic/StoppedPredictableIntegrand.lean at commit e216e28ce3ffb43877e11f71be260e40a37a35df (Apache-2.0), via proved stopping-region theorem ee80bb4f-29d8-45ab-8d46-fd8093074fd0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_gaussian_gradient_stopped_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ := by sorry
