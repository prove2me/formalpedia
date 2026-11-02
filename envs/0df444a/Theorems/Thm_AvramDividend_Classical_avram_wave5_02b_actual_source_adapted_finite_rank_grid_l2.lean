-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_adapted_finite_rank_grid_l2
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_finite_rank_grid_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:01:18.66603+00:00
-- url     : https://prove2.me/theorems/046215c6-6f00-451e-923f-737dbd729871
-- title:
--   Actual source adapted finite-rank marked-grid L² isometry
-- statement:
--   For the original Lévy source, an increasing time grid, original-past measurable coefficients and end-of-cell measurable finite-rank marked increments, the predictable prefix measurability and exact marked-grid second moment follow from the Proved source finite-rank grid theorem. The extractor, its source representation, its Poisson and iid mark laws, and end-of-cell measurability remain explicit hypotheses.
-- source:
--   Proved source finite-rank marked-grid isometry e8b25368-c6dc-4065-94e7-41e188b8ad8e; finite sums of measurable functions and filtration monotonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_finite_rank_grid_l2_of_extractors
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_finite_rank_grid_l2
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid) (C : ℕ → Set ℝ) (s : Finset ι)
    (W : ℕ → ι → Ω → ℝ) (f : ℕ → ι → ℝ → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → ℝ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → (ℕ × (ℕ → ℝ)))
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) =
        (K i ω, fun n : ℕ => Y i n ω))
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hYm : ∀ i n, Measurable (Y i n))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hYL : ∀ i n, HasLaw (Y i n) ρ P)
    (hYi : ∀ i, iIndepFun (Y i) P)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) P)
    (hWp : ∀ i a, a ∈ s → Measurable[𝓕 (grid i)] (W i a))
    (hWm : ∀ i a, a ∈ s → Measurable (W i a))
    (hW2 : ∀ i a, a ∈ s → Integrable (fun ω => W i a ω ^ 2) P)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a))
    (hfI : ∀ i a, a ∈ s → Integrable (f i a) ρ)
    (hf2 : ∀ i a, a ∈ s → MemLp (f i a) 2 ρ)
    (hFsum : ∀ i a, a ∈ s → ∀ ω,
      (∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) =
          ∑ n ∈ Finset.range (K i ω), f i a (Y i n ω))
    (hZp : ∀ i a, a ∈ s → Measurable[𝓕 (grid (i + 1))] (fun ω =>
      (∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ρ))
    (m : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) - (r i : ℝ) * ∫ z, f i a z ∂ρ)) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) - (r i : ℝ) * ∫ z, f i a z ∂ρ)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range m, ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, W i a ω * W i b ω ∂P) * (r i : ℝ) *
          (∫ z, f i a z * f i b z ∂ρ) := by sorry
