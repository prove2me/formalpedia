-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_marked_source_cell_covariance_of_extractor
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_marked_source_cell_covariance_of_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:29:55.67614+00:00
-- url     : https://prove2.me/theorems/57b173a4-7c05-46cb-9b7c-ffde7367dd97
-- title:
--   Actual Lévy marked cell covariance from measurable future extractor and source count laws
-- statement:
--   For the original Lévy source and intrinsic jump measure, two past-measurable square-integrable weights multiply centred marked-cell source sums. If a measurable shifted-future extractor represents the source count and marks, the source rewards have the displayed finite-sum representations, and the stated Poisson and mark laws hold, then the covariance is the product of the predictable weight covariance and the marked-cell intensity. Independence of the past weights and future count-marks is derived from the original Lévy process, not assumed. The extractor, count law, mark laws and source sum representations are explicit remaining hypotheses.
-- source:
--   Proved original future path extractor independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908 and two past weights marked cell covariance 5c54fbf4-25bd-4e56-825f-51fb70d574dc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_past_weights_marked_cell_covariance

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.avram_wave5_02b_actual_marked_source_cell_covariance_of_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (C : Set ℝ)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (H J : Ω → ℝ)
    (hH : Measurable[𝓕 s] H) (hJ : Measurable[𝓕 s] J)
    (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hJ2 : Integrable (fun ω => J ω ^ 2) P)
    (K : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (Fpath : (ℝ≥0 → ℝ) → (ℕ × (ℕ → ℝ)))
    (hFpath : Measurable Fpath)
    (hRep : ∀ ω, Fpath (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
        (K ω, fun n : ℕ => Y n ω))
    (hKsource : ∀ ω, (K ω : ℝ≥0∞) =
      NX ω (Set.Ioc s (s + T) ×ˢ C))
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) P)
    (hYm : ∀ n, Measurable (Y n))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hYL : ∀ n, HasLaw (Y n) ρ P)
    (hYi : iIndepFun Y P)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) P)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfI : Integrable f ρ) (hgI : Integrable g ρ)
    (hf2 : MemLp f 2 ρ) (hg2 : MemLp g 2 ρ)
    (hFsum : ∀ ω,
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) =
        ∑ n ∈ Finset.range (K ω), f (Y n ω))
    (hGsum : ∀ ω,
      (∫ p in Set.Ioc s (s + T) ×ˢ C, g p.2 ∂(NX ω)) =
        ∑ n ∈ Finset.range (K ω), g (Y n ω)) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        (r : ℝ) * ∫ z, f z ∂ρ)
    let B : Ω → ℝ := fun ω => J ω *
      ((∫ p in Set.Ioc s (s + T) ×ˢ C, g p.2 ∂(NX ω)) -
        (r : ℝ) * ∫ z, g z ∂ρ)
    Integrable (fun ω => A ω * B ω) P ∧
      (∫ ω, A ω * B ω ∂P) =
        (∫ ω, H ω * J ω ∂P) * (r : ℝ) * (∫ z, f z * g z ∂ρ) := by sorry
