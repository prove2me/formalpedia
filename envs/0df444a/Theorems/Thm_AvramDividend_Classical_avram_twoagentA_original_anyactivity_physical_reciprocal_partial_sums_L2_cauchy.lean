-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
-- name    : AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:06:54.993555+00:00
-- url     : https://prove2.me/theorems/843c7f98-c5a0-483e-a8ce-1ec81a5ef056
-- title:
--   Actual unrestricted-activity original compensated Lévy reciprocal jump partial sums form an L2-Cauchy sequence
-- statement:
--   For actual original spectrally negative Lévy jump counts, every finite deterministic horizon and arbitrary σ and negative jump activity, the correctly compensated physical reciprocal-mark partial sums have square-integrable pairwise differences whose expected squares converge uniformly to zero. Explicitly reconstructs the partial-sum Cauchy property from the previously proved original compensated annular variance bound and uniform small quadratic Lévy energy, without any abstract or synthetic marked Poisson isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : ℕ → ℕ → Ω → ℝ := fun n m ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, N ≤ m →
        Integrable (fun ω => (F n ω - F m ω) ^ 2) P ∧
          (∫ ω, (F n ω - F m ω) ^ 2 ∂P) < ε := by sorry
