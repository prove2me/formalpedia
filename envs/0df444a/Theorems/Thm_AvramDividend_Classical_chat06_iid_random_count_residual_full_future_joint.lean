-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_full_future_joint
-- name    : AvramDividend.Classical.chat06_iid_random_count_residual_full_future_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:38:13.80842+00:00
-- url     : https://prove2.me/theorems/56ea6a5d-1b86-44ea-bf70-b97ce7121356
-- title:
--   Full joint law of random-count exponential residual and entire post-next-claim renewal suffix
-- statement:
--   For a measurable arrival count N at a fixed observation clock, with all count-selection events almost surely equal to the corresponding finite arrival intervals, let R be the residual of the current iid Exp(1) wait and let G be the complete infinite suffix of waiting times strictly after the next arrival. If every deterministic suffix has one common law mu, then for every nonnegative horizon t and every measurable whole-suffix event B, P(R>t and G in B)=e^(-t)*mu(B). The proof uses the already accepted exact fixed-count residual/future joint factorisation, establishes measurability of the indexed residual and entire suffix functions, and invokes the accepted countable selection gluing theorem. This is a complete random-index joint survival law, though natural-filtration independence, stationary Poisson increments, marks and the final Lévy process witness remain separate formal obligations.
-- source:
--   Source bv_iid_random_count_residual_full_future_joint_chat06_20261021.lean, 58 lines, SHA-256 d993f71a472e07d2f1bdc3188dbd4314c1a9dcbdde34d21cd509688a822e2fb9. Private probe 5d50c432-f867-408d-ae90-8387f22862d1 passed source elaboration to deliberate sentinel with no candidate errors at pinned Mathlib. Official target publication and proof acceptance to follow.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_count_event_residual_future_joint
import Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_future_joint_of_countwise_factorisation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_iid_random_count_residual_full_future_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | t < τ (N ω) ω -
      (clock - ∑ i ∈ Finset.range (N ω), τ i ω) ∧
      (fun j : ℕ => τ (N ω + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B := by sorry
