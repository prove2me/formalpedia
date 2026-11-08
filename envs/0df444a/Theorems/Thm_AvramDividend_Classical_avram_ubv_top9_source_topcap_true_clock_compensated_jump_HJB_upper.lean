-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_true_clock_compensated_jump_HJB_upper
-- name    : AvramDividend.Classical.avram_ubv_top9_source_topcap_true_clock_compensated_jump_HJB_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:35:34.970333+00:00
-- url     : https://prove2.me/theorems/aa31cd1c-d228-42e9-9f2e-cd5a1d42e75d
-- title:
--   Original infinite-cap stopped compensated Taylor jumps plus discounted HJB drift expected upper
-- statement:
--   At any genuine original right-continuous stopping time and finite physical horizon, the original compensated Lévy Taylor jump plus the same-clock discounted generator drift is integrable with nonpositive expectation on a compact positive real reserve band. The global surplus cap is infinite; no finite spatial envelope or new stochastic process is assumed.
-- source:
--   Original accepted stopped jump centring 7061d3d7 and original topcap stopped generator HJB signed L1 9fc26519, feeding physical witness 25573e81 and canonical 148b2516.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_source_topcap_true_clock_compensated_jump_HJB_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ) (u v δ B : ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    let M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := P.bind K
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
    let MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := M.restrict S
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))),
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
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
      let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
      let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1.1 ≤ σ p.1.2 then GW p else 0
      let ρ : ℝ≥0 × Ω → ℝ := fun p =>
        if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
      let R : ℝ≥0 × Ω → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (ρ p * (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
      let Z : Ω → ℝ := fun ω =>
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) +
        (∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0
          ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 := by sorry
