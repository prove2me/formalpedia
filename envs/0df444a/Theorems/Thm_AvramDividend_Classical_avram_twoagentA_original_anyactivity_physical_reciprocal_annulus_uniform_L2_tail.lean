-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
-- name    : AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:58:53.661045+00:00
-- url     : https://prove2.me/theorems/7fc35320-a48d-4672-ab06-94d0e53f559e
-- title:
--   Unrestricted-activity original physical compensated reciprocal annular jump sums have uniform vanishing L2 tails
-- statement:
--   For any genuine spectrally negative Levy process with arbitrary negative jump activity and Gaussian coefficient, and any deterministic time horizon T, prove a uniform-in-m finite L2 tail estimate as n tends to infinity for actual original physical compensated reciprocal mark-annulus counts from n to m. All tail square integrals are finite, and their expectations approach zero uniformly over m at or above n. The bound is derived from the original Levy quadratic integrability. No finite activity, auxiliary compensated Poisson noise, abstract L2 isometric map, or supplied summability assumption is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
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
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, n ≤ m →
        Integrable (fun ω => (S n m ω) ^ 2) P ∧
          (∫ ω, (S n m ω) ^ 2 ∂P) < ε := by sorry
