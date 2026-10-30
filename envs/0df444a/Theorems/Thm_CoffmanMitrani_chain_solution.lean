-- Prove2me | Theorems.Thm_CoffmanMitrani_chain_solution
-- name    : CoffmanMitrani.chain_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:43.839581+00:00
-- url     : https://prove2.me/theorems/608dae3b-5556-447c-80b1-dc69ed1dae36
-- title:
--   Proof of Lemma 2: (5) on a chain is solved precisely by $P(i_1,\dots,i_M)$
-- statement:
--   Let $S$ be a scheduling strategy following the preemptive priority discipline that gives priority in the order $i_1, i_2, \dots, i_M$, and let $P(i_1,\dots,i_M)$ be its performance vector. For the sets $g_k = \{i_1,\dots,i_k\}$, $k = 1,\dots,M$, a vector $\hat W$ satisfies the $M$ equations
--   $$\sum_{i\in g_k}\rho_i \hat W_i = \frac{\sum_{i\in g_k}\rho_i/\mu_i}{1-\sum_{i\in g_k}\rho_i}, \qquad k = 1,\dots,M, \qquad (5)$$
--   if and only if $\hat W = P(i_1,\dots,i_M)$.
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
--   - reading: the solution of (5) for these subsets is precisely P(i1, i2, ···, iM) → W' solves (5) on the chain iff W' = P(σ); reason: "precisely" asserts both that P(σ) solves (5) and that it is the only solution
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2

import Mathlib
import Definitions.Def_CoffmanMitrani_IsPriority
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_Data_loadBound
import Definitions.Def_CoffmanMitrani_chain

namespace CoffmanMitrani

/-- **The solution of (5) on a chain is the priority vector.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2: "Thus we must have (perhaps after renumbering) g1 = {i1},
g2 = {i1, i2}, ···, gM−1 = {i1, i2, ···, iM−1}, gM = {i1, i2, ···, iM} = {1, 2, ···, M} for some
i1, i2, ···, iM ∈ {1, 2, ···, M} such that ij ≠ ik; j ≠ k. The proof of Lemma 2 is completed by
remarking that the solution of (5), for these subsets of job class indices, is precisely
P(i1, i2, ···, iM)."

Let `S` be a scheduling strategy implementing the preemptive priority discipline `σ` and achieving
`W` (the paper's `P(σ)`). Then a vector `W'` satisfies the `M` equations
`Σ_{i ∈ chain σ k} ρi W'i = (Σ_{i ∈ chain σ k} ρi/μi)/(1 − Σ_{i ∈ chain σ k} ρi)`, `k = 0, …, M − 1`,
if and only if `W' = W`.

**Formalization Note.** `chain σ k = {σ 0, …, σ k}` is the paper's `g_{k+1}` with
`σ l = i_{l+1} − 1`. "Precisely" is read as both directions: `P(σ)` solves (5) and is its only
solution. -/
theorem chain_solution (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M)
    (W : Fin D.M → ℝ) (hP : IsPriority D σ S) (hS : IsStrategy D S) (hW : Achieves D S W)
    (W' : Fin D.M → ℝ) :
    (∀ k : Fin D.M, ∑ i ∈ chain σ k, D.rho i * W' i = D.loadBound (chain σ k)) ↔
      W' = W := by sorry

end CoffmanMitrani
