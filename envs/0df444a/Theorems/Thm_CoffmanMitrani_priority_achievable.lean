-- Prove2me | Theorems.Thm_CoffmanMitrani_priority_achievable
-- name    : CoffmanMitrani.priority_achievable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:24:56.52667+00:00
-- url     : https://prove2.me/theorems/e14b429d-ef17-4406-a9b2-731f3aecc662
-- title:
--   The preemptive priority disciplines have performance vectors
-- statement:
--   For every assignment of priorities to the $M$ classes there is a scheduling strategy that follows the corresponding preemptive priority discipline and achieves a performance vector, namely $P(i_1,\dots,i_M)$.
--
--   These $M!$ vectors span the set $H$ of definition (3).
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
--   - encoding: Poisson arrivals and exponential services, mutually independent; randomized strategies governed by some probability law (Assumption 3) → canonical product space of exponential interarrival times, exponential service requirements and i.i.d. uniform seed sequences per job; a randomized strategy is a function of the seeds of the job that opens the current busy period; reason: every randomized decision law can be generated from i.i.d. uniform seeds; one seed sequence per busy period keeps busy periods independent
--   - reading: Assumptions 2–3: S(t) restricted to arrival times, departure times, execution intervals and class indices of the jobs of the current busy period B up to time t, and no information from prior busy periods → IsStrategy clause 5: S(t) = rule(record of the current busy period up to t, with relative times and within-busy-period ranks; that busy period's seeds), one rule for all busy periods; reason: formal content of 'the domain of S(t) is restricted to'; it excludes service requirements not yet revealed, future arrivals, absolute time and the busy-period count
--   - encoding: S(t) a random mapping; Assumption 1 (no idling iff idle period); jobs eventually served → joint null-measurability of S, and clauses 2–4 of IsStrategy required almost surely, including a completion clause; reason: measurability is needed for wi(n) to be a random variable; completion follows almost surely from Assumption 1 and ρ < 1, and makes departure times well defined
--   - encoding: busy and idle periods defined through the presence of jobs requiring service → busy periods defined from the arrival and service data (IsBPStart, InBP); reason: under Assumption 1 the busy periods are the same for every strategy (p. 813)
--   - encoding: Wi = lim_{n→∞} E(wi(n)), whose existence is assumed → every wi(n) integrable and E(wi(n)) → Wi; reason: rules out the junk value ∫ = 0 of a non-integrable function; under ρ < 1 response times of strategies are integrable
--   - encoding: S(i1, …, iM): preemptive priority with class i1 highest → IsPriority σ with σ k = i_{k+1} − 1, σ 0 highest; reason: 0-based classes
--   - reading: preemptive priority discipline (order within a class unspecified) → first come first served within a class (preemptive resume); reason: the paper does not fix the order within a class; it does not change any class mean
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 815; p. 816 (proof of Theorem 2, "(achievable) preemptive priority disciplines")

import Mathlib
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves

namespace CoffmanMitrani

/-- **The preemptive priority disciplines are scheduling strategies with a performance vector.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 816, proof of Theorem 2: "Identifying the Sj's in Theorem 1 with the (achievable)
preemptive priority disciplines"; p. 815: "the performance vectors of the preemptive priority
disciplines … There are M! such disciplines, one for each assignment of priorities to the M job
classes."

For every priority order `σ` there is a scheduling strategy implementing the preemptive priority
discipline `σ` and achieving some performance vector `W` (the paper's `P(σ)`).

**Formalization Note.** `σ 0` is the class of highest priority; first come first served within a
class. -/
theorem priority_achievable (D : Data) (σ : Equiv.Perm (Fin D.M)) :
    ∃ (S : Schedule D.M) (W : Fin D.M → ℝ),
      IsPriority D σ S ∧ IsStrategy D S ∧ Achieves D S W := by sorry

end CoffmanMitrani
