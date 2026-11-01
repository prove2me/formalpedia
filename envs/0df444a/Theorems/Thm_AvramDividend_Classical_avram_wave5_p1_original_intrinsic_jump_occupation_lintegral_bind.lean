-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:07:44.168975+00:00
-- url     : https://prove2.me/theorems/a2b399cb-efbd-4522-b560-a6e7e55207e7
-- title:
--   Original Lévy intrinsic jump occupation has nonnegative source Fubini identity under explicit predictable kernel measurability
-- statement:
--   For the unchanged original Lévy path X, NX(ω) is its literal jump-time/mark counting measure. If the lifted sample-wise measures Kω on the original predictable time-path×mark space are measurable as a measure-valued kernel, and M is their bind against the original probability P, then every nonnegative predictable measurable reward has the exact iterated source-jump expectation formula. Requires and exposes kernel measurability and pathwise predictable lift measurability; does not infer the source Poisson count law, compensator equality, integrability or signed Fubini.
-- source:
--   Mathlib Measure.lintegral_bind and lintegral_map at pinned revision, with literal SpectrallyNegativeLevy intrinsic jump NX. A missing measure-theoretic prerequisite for the proved stopped signed source transfer UUID f544dab9-21ae-4ce6-b2a1-1c4041802831; the original Lévy predictable rectangle law is independently Open and owned by Chat 01.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (hLift : ∀ ω,
      @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H) :
    (∫⁻ p, H p ∂M) =
      ∫⁻ ω, ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P := by sorry
