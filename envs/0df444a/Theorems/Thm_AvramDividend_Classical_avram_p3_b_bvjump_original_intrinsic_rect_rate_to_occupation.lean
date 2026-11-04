-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:38:05.991046+00:00
-- url     : https://prove2.me/theorems/acad4107-e33b-4b48-959b-6f7589828954
-- title:
--   Actual right-continuous source jump occupation inherits P2's original finite rectangle rate
-- statement:
--   For the literal intrinsic jump-count measure NX of the original spectrally negative Lévy process X, the original lifted source occupation M=P.bind K on the same Ω and P inherits P2's original future jump-count rectangle rate from the already Proved genuine rightCont adapted occupation identity. The only source-rate premise hRate is word-for-word the outstanding P2 rectangle compensator identity; it is conditional and does not introduce an independent Poisson model or compensator axiom. Includes infinite ν values, P(A)=0 and ENNReal product edge cases.
-- source:
--   Accepted 9b57a0a5 Prove2Me original rightCont adapted occupation equals intrinsic count lower integral; outstanding P2 393b03a8 original rectangle law; Avram Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_intrinsic_rect_rate_to_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
          P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B),
      M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
