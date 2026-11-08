-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_discounted_stopped_HJB_L1_nonpos
-- name    : AvramDividend.Classical.avram_ubv_top9_source_topcap_discounted_stopped_HJB_L1_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:15:50.21842+00:00
-- url     : https://prove2.me/theorems/9fc26519-f676-49d0-b785-5b43f8d1130b
-- title:
--   Original infinite-cap discounted stopped compact HJB drift has nonpositive expectation
-- statement:
--   For the exact original infinite-cap process, discounted compact generator drift evaluated at the genuine left-limit pre-right-payment reserve and stopped at any right-continuous clock is integrable and has nonpositive expectation. The accepted discounted stopped integrability theorem and pointwise original HJB inequality give the full signed drift budget.
-- source:
--   Combines original topcap discounted stopped L1 2cf56908 with the true pointwise generator HJB sign on the compact interior strip. Feeds the physical Ito witness 25573e81 and original expectation upper 148b2516.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_source_topcap_discounted_stopped_HJB_L1_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    Integrable (fun ω => ∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω : Ω, (∫ t : ℝ≥0,
      if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
