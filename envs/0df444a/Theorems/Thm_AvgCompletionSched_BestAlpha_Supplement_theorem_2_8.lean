-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_Supplement_theorem_2_8
-- name    : AvgCompletionSched.BestAlpha.Supplement.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:52:34.251252+00:00
-- url     : https://prove2.me/theorems/1b6b2440-fff8-4fbb-a6e1-a9091eec099f
-- title:
--   Theorem 2.8 — polynomial-time randomized online e/(e−1)-competitive scheduling
-- statement:
--   There is one randomized causal nonpreemptive one-machine policy $A$, fixed before every input, which samples one shared $a\in(0,1]$ with density $e^a/(e-1)$ and runs the counted SRPT event simulation and insertion-time FIFO queue. On every finite input $I$ with positive processing times and nonnegative release dates, the simulation terminates, every job receives exactly one reservation, and the resulting starts form a feasible schedule. Its cost is measurable and integrable. For every feasible offline nonpreemptive schedule $N$ of the same fixed input,
--
--   $$\mathbb E_a\!\left[\sum_j C^{A(I,a)}_j\right]\le\frac{e}{e-1}\sum_j C^N_j.$$
--
--   There are uniform constants $K>0$ and $d\in\mathbb N$, independent of the input and seed, such that the implementation's counted arithmetic/comparison/read/write operations, including output extraction, satisfy
--
--   $$\operatorname{operations}(I,a)\le K(n+1)^d.$$
--
--   The theorem establishes the event evaluator's termination and semantics, SRPT optimality, and prefix consistency even when unseen future jobs and their total number change. No efficiency, feasible output, optimal oracle or integrability condition is assumed. The seed is drawn before the fixed input, so the adversary is oblivious. The objective is unweighted total completion time; there are no precedence constraints. Empty inputs are included and have zero cost. This companion supplies both the online and computational clauses of the source result, independently of the published offline goal.
--
--   Differences from the source:
--   - encoding: a randomized on-line algorithm unaware of each job before its release → one event policy fixed before all inputs, prefix consistency for identical revealed histories across different future job counts, one shared exponential seed independent of input; reason: this makes the source oblivious-adversary information model explicit without limiting finite instances
--   - encoding: simulate SRPT and execute FIFO respecting α-point insertion times → least-remaining-work event scans with fixed job-label ties, unique reservations, feasible preemptive and nonpreemptive realizations and the insertion-time FIFO recurrence as conclusions; reason: the offline release-time α-schedule is not the online output; no optimal-schedule oracle or existence premise is assumed
--   - encoding: polynomial-time implementation → an explicit counted exact-real event implementation with one K>0 and natural exponent d before all inputs and seeds, operations at most K(n+1)^d; reason: direct scans give a polynomial implementation in the scheduling arithmetic/comparison model; the external environment supplies releases, waiting is free, and the single exact density sample is initial randomness, not a finite-bit sampler claim
--   - encoding: expected competitive ratio e/(e−1) → a probability seed law, measurable start functions, integrable total cost and the exact expectation bound against every feasible offline nonpreemptive schedule; reason: this states the full multiplicative guarantee with no additive slack and prevents a nonintegrable Bochner integral from defaulting to zero
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, DOI 10.1137/S0097539797327180, pp. 155–156, Theorem 2.8

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Online

set_option autoImplicit false

namespace AvgCompletionSched.BestAlpha.Supplement

open MeasureTheory

/-- Theorem 2.8, p.155: one fixed randomized causal policy, with a counted event
implementation and a uniform polynomial bound. Its single seed has the exponential
law independent of input. Feasibility, termination, SRPT realization, FIFO eligibility,
measurability and integrability are all conclusions, not oracle assumptions. -/
theorem theorem_2_8 :
    ∃ A : Policy,
      A = (fun _ I a => eventStart I a) ∧
      Causal A ∧ IsProbabilityMeasure alphaLaw ∧
      alphaLaw (Set.Ioc (0 : ℝ) 1) = 1 ∧
      ∃ (K : ℝ) (d : ℕ), 0 < K ∧
        ∀ (n : ℕ) (I : Instance n),
          (∀ a ∈ Set.Ioc (0 : ℝ) 1,
            Finished (eventRun I a) ∧
            (implementationOperations I a : ℝ) ≤ K * ((n : ℝ) + 1) ^ d ∧
            ∃ (P : PreemptiveSchedule I) (N : NonpreemptiveSchedule I),
              IsSRPT P ∧ OptimalPreemptive P ∧ RealizesQueue A I a P ∧
              N.S = A n I a) ∧
          (∀ j, Measurable (fun a : Set.Ioc (0 : ℝ) 1 => A n I a.val j)) ∧
          Integrable (onlineCost A I) alphaLaw ∧
          ∀ N : NonpreemptiveSchedule I,
            (∫ a, onlineCost A I a ∂alphaLaw) ≤
              (Real.exp 1 / (Real.exp 1 - 1)) * weightedCost (fun _ => 1) N := by sorry

end AvgCompletionSched.BestAlpha.Supplement
