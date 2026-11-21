-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_positiveclock_ito_positive_excess_ae_and_domination_source
-- name    : AvramDividend.Classical.avram_pj_original_strict_positiveclock_ito_positive_excess_ae_and_domination_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:51:03.491234+00:00
-- url     : https://prove2.me/theorems/66b70a18-6e4d-4d97-a202-a7afcebefd22
-- title:
--   Original genuine stopped full negative-mark positive Ito excess almost-sure convergence with one integrable domination
-- statement:
--   For the exact original pure-jump spectrally negative Levy controlled reserve and strictly positive stopped physical clocks, there is an epsilon-chosen spatial compact C2 band, full negative nonlinear marked jump J, once-counted generator B and small linear mark L, with an integrable small spatial envelope K, and a common integrable original sample-path bound M such that the masked positive one-sided physical signed Ito residual E_k is integrable, dominated in absolute value by M and tends to zero almost everywhere as the true original full physical mesh refines. This is the real pathwise stochastic Ito Taylor/compensator convergence and domination obligation; unlike the earlier overly strong absolute signed residual source it never requires negative continuous-gradient dividend loss to vanish. Mathlib dominated convergence already Proved via 4e3a6978 implies the parent exact positive L1 source 35e57d4e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_strict_positiveclock_ito_positive_excess_ae_and_domination_source {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
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
      let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
        ((Finset.range (k + 1)).image
          (fun i : ℕ => min
            ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
            (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
      let Q : ℕ → Ω → ℝ := fun k ω =>
        if ρ ω = 0 then 0 else ∑ t ∈ A k ω, Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
             w (riskProcess X x D t ω -
               (rightLimit D t ω - D t ω))))
      ∃ (K M : Ω → ℝ),
        Integrable K P ∧
        (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
        (∀ ω, ρ ω = 0 → K ω = 0) ∧
        Integrable M P ∧
        (∀ k : ℕ, Integrable (fun ω =>
          if ρ ω = 0 then 0
          else max (0 : ℝ) (V ω - U ω - K ω - Q k ω)) P) ∧
        (∀ k : ℕ, ∀ᵐ ω ∂P,
          |if ρ ω = 0 then (0 : ℝ)
            else max (0 : ℝ) (V ω - U ω - K ω - Q k ω)| ≤ M ω) ∧
        (∀ᵐ ω ∂P, Tendsto
          (fun k : ℕ => if ρ ω = 0 then (0 : ℝ)
            else max (0 : ℝ) (V ω - U ω - K ω - Q k ω))
          Filter.atTop (𝓝 (0 : ℝ)))) := by sorry
