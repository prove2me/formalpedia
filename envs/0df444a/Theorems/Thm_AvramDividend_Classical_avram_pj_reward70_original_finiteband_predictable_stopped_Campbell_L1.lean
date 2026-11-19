-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
-- name    : AvramDividend.Classical.avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:30:48.326928+00:00
-- url     : https://prove2.me/theorems/7bf1984f-5e17-47ba-aaf8-0af43b57e5d1
-- title:
--   Original finite-band bounded predictable marked X-jump compensated integral has stopped L1 mean zero
-- statement:
--   For the actual spectrally negative Levy process X with its intrinsic marked jump measure and deterministic finite horizon T, any real-valued predictable bounded kernel supported in negative Borel marks B of finite Levy intensity and t<=T yields an integrable compensated stopped marked jump integral of unconditional expectation zero for any stopping time of the right-continuous filtration. Uses the actual physical intrinsic X jump measure and actual dt-times-Levy measure, including stopped endpoints; a generic finite-band compensated Campbell/optional-stopping theorem, without assumptions already equivalent to its conclusion.
-- source:
--   Proof-support decomposition of Avram-Palmowski-Pistorius (2007) Proposition 4(i), physical finite-band stopped compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hBNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤)
    (F : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F)
    (hSupport : ∀ p, (T < p.1.1 ∨ p.2 ∉ B) → F p = 0)
    (C : ℝ) (hC : 0 ≤ C) (hBound : ∀ p, |F p| ≤ C)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
  (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
   let μT : Measure ℝ≥0 :=
     ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
   let Z : Ω → ℝ := fun ω =>
     (∫ p, (if p.1 ≤ σ ω then F ((p.1, ω), p.2) else 0) ∂(NX ω)) -
     (∫ t, ∫ z, (if t ≤ σ ω then F ((t, ω), z) else 0)
       ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
   Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0) := by sorry
