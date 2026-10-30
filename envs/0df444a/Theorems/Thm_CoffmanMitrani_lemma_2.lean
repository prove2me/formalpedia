-- Prove2me | Theorems.Thm_CoffmanMitrani_lemma_2
-- name    : CoffmanMitrani.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:57.673108+00:00
-- url     : https://prove2.me/theorems/138a6c57-7605-46f9-9548-bc662b78dc86
-- title:
--   Lemma 2: vertices of $H^{**}$ are priority vectors
-- statement:
--   Let $H^{**}$ be the set of vectors satisfying the conservation law (1) and the $2^M-2$ inequalities (4) for the proper nonempty subsets $g$. Then every vertex of $H^{**}$ coincides with one of the preemptive priority vectors $P(1,2,\dots,M),\dots,P(M,M-1,\dots,1)$: it is the performance vector of a scheduling strategy that follows some preemptive priority discipline.
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
--   - encoding: vertex of H** → extreme point of H** (Set.extremePoints ℝ); reason: for a polyhedron the vertices are its extreme points
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, Lemma 2

import Mathlib
import Definitions.Def_CoffmanMitrani_Hss
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves

namespace CoffmanMitrani

/-- **Lemma 2.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, Lemma 2: "Let H** be the set of performance vectors which satisfy the
conservation law (1) and the 2^M − 2 inequalities (4), where g runs through all the proper nonempty
subsets of {1, 2, ···, M}. Then, every vertex of H** coincides with one of the preemptive priority
vectors P(1, 2, ···, M), ···, P(M, M − 1, ···, 1)."

Every extreme point `W` of `H**` is the performance vector achieved by a scheduling strategy
implementing some preemptive priority discipline `σ`.

**Formalization Note.** "Vertex" is Mathlib's `Set.extremePoints ℝ`. -/
theorem lemma_2 (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ Set.extremePoints ℝ (Hss D)) :
    ∃ (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M),
      IsPriority D σ S ∧ IsStrategy D S ∧ Achieves D S W := by sorry

end CoffmanMitrani
