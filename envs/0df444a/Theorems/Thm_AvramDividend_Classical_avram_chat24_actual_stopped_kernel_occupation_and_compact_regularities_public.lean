-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_actual_stopped_kernel_occupation_and_compact_regularities_public
-- name    : AvramDividend.Classical.avram_chat24_actual_stopped_kernel_occupation_and_compact_regularities_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:05:31.617091+00:00
-- url     : https://prove2.me/theorems/434a944f-a6f4-4b64-8aa8-8554ba093a5c
-- title:
--   Actual stopped kernel occupation L1 and compact time regularity
-- statement:
--   Source-faithful analytical certificate for 10ef35ab-e13b-45f3-9ed8-046c77d64038. Retain actual X,D,ruin time, positive shift, compact band, actual jump source, physical clock and target H. The certificate isolates occupation L1, predictable measurability, the nonempty compact reserve band and C1 drift/discount continuity. Norm Fubini and bounded finite-clock integration formally imply the original two pathwise integrability obligations. This is stronger intermediate mathematical data, not a restatement of pathwise integrability. Published as a public prerequisite because the authoritative parent is public and public candidates cannot import private helper declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_actual_stopped_kernel_occupation_and_compact_regularities_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 ≤ x) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let Ξ : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) inferInstance
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)) (NX ω)
    a ≤ b ∧ Measurable[𝓕.rightCont.predictable] Y ∧
    ContinuousOn (fun y => X.drift * deriv w y - q * w y) (Icc a b) ∧
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] H ∧ Integrable H (P.bind Ξ) := by sorry
