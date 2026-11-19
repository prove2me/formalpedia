-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward60_original_compact_smallmark_all_stops_zero_mean
-- name    : AvramDividend.Classical.avram_pj_reward60_original_compact_smallmark_all_stops_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:49:33.376194+00:00
-- url     : https://prove2.me/theorems/e64b3b67-7f0d-4b70-91dd-d11b5337454e
-- title:
--   Original finite-band actual X marked stopped linear source is centred in L1 for every stopping clock
-- statement:
--   For the exact original intrinsic spectrally negative Lévy jump measure, fixed horizon T, original stopped prepayment left-limit Y and the discounted compact spatial derivative on strictly negative finite-cutoff marks, the stopped jump integral minus its physical dt-times-Lévy compensator is L1 and has mean zero for every right-continuous stopping clock. The finite horizon indicator is inside H, so this statement remains correct when σ>T. This is the missing physical Campbell/compensation premise for initial-event source42 via the already Proved initial-event masking lemma eb05cecc.
-- source:
--   Original spectral-negative Levy jump counting process, source-pinned predictable rightCont filtration and finite-mark compensation; Proved 7190391d masked finite grid, d861d958 physical gradient MemLp, a4a6f84f mark size MemLp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward60_original_compact_smallmark_all_stops_zero_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband) (hvC : v < C.toReal)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
  (let T : ℝ≥0 := (n : ℝ≥0)
   let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
     (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
   let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
     ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
       Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
   let μT : Measure ℝ≥0 :=
     ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
   let H : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
     if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
       Real.exp (-(q * (p.1 : ℝ))) *
         (if Y (p.1, ω) ∈ Icc (u + δ) v then
           deriv w (Y (p.1, ω)) * p.2 else 0) else 0
   ∀ σ : Ω → ℝ≥0,
     IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)) →
     Integrable (fun ω =>
       (∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) P ∧
     (∫ ω, ((∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) ∂P) = 0) := by sorry
