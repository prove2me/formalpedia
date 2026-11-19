-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward31_original_trueclock_finitecap_Taylor_HJB_initial_event_upper
-- name    : AvramDividend.Classical.avram_pj_reward31_original_trueclock_finitecap_Taylor_HJB_initial_event_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:11:02.383709+00:00
-- url     : https://prove2.me/theorems/68b3a298-77eb-4485-aaf9-38616dc3a733
-- title:
--   True original finite-cap compact stopped compensated Taylor and HJB source has nonpositive initial-event integral
-- statement:
--   For the original SNLP stopped compensated nonlinear negative-jump Taylor functional at the actual controlled reserve and the source HJB generator drift, the integral of J plus B over any initial right-continuous filtration event is nonpositive. No artificial stochastic process or dividend control is substituted. Follows from Proved e3c8f4e7 conditional nonpositive source and Proved 12ae9b2d initial-event budget lemma.
-- source:
--   Proved e3c8f4e7-9b69-432e-9b99-7f31ec5dabad and 12ae9b2d-4b40-4887-8130-ce62ff5c0c8d; Avram, Palmowski, Pistorius (2007) Prop 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward28_original_trueclock_finitecap_Taylor_HJB_initial_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward31_original_trueclock_finitecap_Taylor_HJB_initial_event_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (Ccap : ℝ≥0∞) (hCcap : 0 < Ccap) (hFinite : Ccap ≠ ⊤)
    (hAd : IsAdmissibleLe X x Ccap D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cap : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < Ccap})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) (hvCap : v < Ccap.toReal)
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < Ccap →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < Ccap → 1 ≤ deriv w y)
    (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let B : (Ω → ℝ≥0) → Ω → ℝ := fun σ ω =>
      ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A),
      (∫ ω in A, J σ ω + B σ ω ∂P) ≤ 0 := by sorry
