-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_renewal_residual_future_from_ae_threshold
-- name    : AvramDividend.Classical.avram_a06_renewal_residual_future_from_ae_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:34:40.557486+00:00
-- url     : https://prove2.me/theorems/ed6891bd-b40a-48a4-815d-6bdd71e345d9
-- title:
--   Almost-sure arrival threshold implies exponential residual and full infinite future suffix joint law
-- statement:
--   The known iid exponential full-future residual law only requires the exact arrival-count threshold on a full-measure set, which is available on the original compound-Poisson driver.
-- source:
--   Lift the chat06 exact count-cylinder identity through the common full-measure threshold event and invoke the proved chat06 iid random-count residual/full-future joint theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_full_future_joint
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_renewal_residual_future_from_ae_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | t < τ (N ω clock) ω -
      (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B := by sorry
