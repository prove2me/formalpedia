-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_marked_stopped_grid_isometry_of_extractors
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_marked_stopped_grid_isometry_of_extractors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:31:15.690937+00:00
-- url     : https://prove2.me/theorems/71be2502-a3f2-41f9-919d-bf754613905d
-- title:
--   Actual stopped marked finite-grid L² isometry from source path extractors and cell laws
-- statement:
--   For the original Lévy source, intrinsic marked jump measure and actual stopped grid-cell jump integrals, a finite-grid L² isometry holds when the explicit measurable source extractors, source-sum representations and marked Poisson laws are supplied. The coefficient and prefix are measurable in the original past, and independence of each from the future marked cell follows from the original Lévy process. The source representation and marked laws remain hypotheses; this does not assert a sigma-finite tail bound or prove the laws.
-- source:
--   Proved original future path extractor independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908 and finite grid stopped marked L² isometry 45bd3136-3903-40f7-866d-24438e4eb8bf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave5_02b_actual_marked_stopped_grid_isometry_of_extractors
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ)
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → ℝ)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → (ℕ × (ℕ → ℝ)))
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) =
        (K i ω, fun n : ℕ => Y i n ω))
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hKm : ∀ i, Measurable (K i))
    (r : ℕ → ℝ≥0)
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hYm : ∀ i n, Measurable (Y i n))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hYL : ∀ i n, HasLaw (Y i n) ρ P)
    (hYi : ∀ i, iIndepFun (Y i) P)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) P)
    (hW : ∀ i, Measurable[𝓕 (grid i)]
      (fun ω => if i < τ ω then H i ω else 0))
    (hWm : ∀ i, Measurable
      (fun ω => if i < τ ω then H i ω else 0))
    (hW2 : ∀ i, Integrable
      (fun ω => (if i < τ ω then H i ω else 0) ^ 2) P)
    (f : ℕ → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hfI : ∀ i, Integrable (f i) ρ) (hf2 : ∀ i, MemLp (f i) 2 ρ)
    (hFsum : ∀ i ω,
      (∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i p.2 ∂(NX ω)) =
          ∑ n ∈ Finset.range (K i ω), f i (Y i n ω))
    (hIncMeas : ∀ i, Measurable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ρ)))
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ρ)))
    (hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ρ)))
    (m : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range m,
        (if i < τ ω then H i ω else 0) *
          ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
              f i p.2 ∂(NX ω)) -
            (r i : ℝ) * ∫ z, f i z ∂ρ)) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range m,
      (if i < τ ω then H i ω else 0) *
        ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
            f i p.2 ∂(NX ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ρ)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range m,
        (∫ ω, (if i < τ ω then H i ω else 0) ^ 2 ∂P) *
          ((r i : ℝ) * ∫ z, f i z ^ 2 ∂ρ) := by sorry
