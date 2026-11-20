-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_original_physical_two_stage_signed_mesh_source
-- name    : AvramDividend.Classical.avram_pj_workerC_strict_original_physical_two_stage_signed_mesh_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T08:10:06.049156+00:00
-- url     : https://prove2.me/theorems/272918cd-1d77-4122-b758-258b06b209fa
-- title:
--   Physical purejump stopped signed Ito mesh K/E/Q source with jointly selected C2 spatial and negative-mark cutoffs
-- statement:
--   Under exact original sigma=0 unbounded-variation spectrally negative Lévy, finite cap, actual stopped ruin-clipped rho, and original postpayment terminal and strict prepayment cash, select spatial band and negative Lévy cutoff and construct a genuine integrable signed residual K with L1 <= epsilon/4, vanishing L1 mesh error E and nonpositive HJB/payment term Q. For every finite mesh, V-U<=K+E+Q. Terminal/strict cash integrability is handled independently by a proved public result and not postulated here. This is the remaining physical stochastic Ito assembly.
-- source:
--   Original ef4b strict prepayment two-stage source, selected accepted reduction 26a97ade; exact four-term original grid and compensated negative jump source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_strict_original_physical_two_stage_signed_mesh_source {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Cband u v δ η : ℝ,
        0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧ 0 < η ∧ η < 1 ∧
        v < Cband ∧ v < C.toReal ∧
        ContDiffOn ℝ 2 w (Ioo 0 Cband) ∧
      (let T : ℝ≥0 := (n : ℝ≥0)
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
      let L : Ω → ℝ := fun ω =>
        (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if Y (p.1, ω) ∈ Icc (u + δ) v then
              deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω)) -
        (∫ t, ∫ z,
          (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then
            Real.exp (-(q * (t : ℝ))) *
              (if Y (t, ω) ∈ Icc (u + δ) v then
                deriv w (Y (t, ω)) * z else 0) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      let U : Ω → ℝ := fun ω => w x + (J ρ ω + B ρ ω + L ω)
      let V : Ω → ℝ := fun ω =>
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      ∃ (K : Ω → ℝ) (E Q : ℕ → Ω → ℝ),
        Integrable K P ∧
        (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
        (∀ k, Integrable (E k) P) ∧
        (∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0) ∧
        (∀ k, ∀ᵐ ω ∂P, V ω - U ω ≤
          K ω + E k ω + Q k ω) ∧
        Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
          Filter.atTop (𝓝 (0 : ℝ))) := by sorry
