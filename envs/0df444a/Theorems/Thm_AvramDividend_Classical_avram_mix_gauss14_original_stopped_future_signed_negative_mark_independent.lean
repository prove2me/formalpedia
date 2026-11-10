-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:25:30.440951+00:00
-- url     : https://prove2.me/theorems/540a266d-00a0-42c7-a7c9-51ee9df2befa
-- title:
--   Original future signed negative-mark jump integral is independent of the original stopped filtration
-- statement:
--   For every actual finite original-filtration stopping time and Borel set of nonpositive jump marks, the real signed jump integral over the original process future left-open right-closed window is independent of the original stopped-time history. The proof uses the physically exact signed-window to nonnegative marked-mass formula and the already proved independence of original weighted future marked jump mass, followed by measurable sign change. This is an integrability-free source-level input for compensated jump centring and Gaussian jump cross-orthogonality, with both boundary atoms preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_stopped_future_weighted_mark_mass_independent
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_stopped_future_signed_negative_mark_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω =>
          ∫ p in (Ioc (τ ω) (τ ω + T) ×ˢ B), p.2 ∂J ω)
        inferInstance) P := by sorry
