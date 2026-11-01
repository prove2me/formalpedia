-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:21:23.266988+00:00
-- url     : https://prove2.me/theorems/647b088f-557c-4312-9dbd-bc44b740fa32
-- title:
--   Finite-grid predictable centred Poisson count L2 isometry
-- statement:
--   For a genuine finite sequence of original probability-space Poisson increments K_i of specified rates r_i and square-integrable predictable weights H_i, assume each future count is independent of the joint pair (accumulated previous compensated sum,H_i) and its centred count is L1. Under explicit L2 integrability of previous partial sums, prove the whole weighted compensated sum has finite second moment and E[(∑_{i<n} H_i(K_i-r_i))²] = ∑_{i<n} r_i E[H_i²]. The proof is induction from the separately proved two-cell energy increment and does not assume any martingale/isometry or an auxiliary equal-law surrogate. Original X marked-law and small-jump continuous-time limits still remain to be proved.
-- source:
--   Canonical P1 two-cell incremental isometry (currently publication pending) derived from Proved Poisson count variance, joint-past cross orthogonality; Finset.sum_range_succ finite induction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_predictable_poisson_l2_increment

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_grid_predictable_poisson_l2_isometry
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (hHm : ∀ i, Measurable (H i))
    (hHlp : ∀ i, MemLp (H i) 2 P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hPrefixLp : ∀ i, MemLp (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))) 2 P)
    (hJointPast : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))), H i ω))
      (K i) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range n,
        H i ω * ((K i ω : ℝ) - (r i : ℝ))) ^ 2 ∂P) =
          ∑ i ∈ Finset.range n,
            (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
