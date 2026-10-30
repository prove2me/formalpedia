-- Prove2me | Theorems.Thm_CoffmanMitrani_theorem_2
-- name    : CoffmanMitrani.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:23.290709+00:00
-- url     : https://prove2.me/theorems/1dad8aff-507d-4418-998c-1ad0cefa0131
-- title:
--   Theorem 2: achievable vectors are the convex hull of the preemptive priority vectors
-- statement:
--   Consider $M \ge 1$ job classes with Poisson arrivals at rates $\lambda_i > 0$, exponential service times with parameters $\mu_i > 0$, all mutually independent, and $\rho = \sum_i \lambda_i/\mu_i < 1$. A vector $\hat W = (\hat W_1,\dots,\hat W_M)$ is achievable by some scheduling strategy — a strategy that never idles while a job is present and whose decisions in a busy period depend only on the arrival times, departure times, execution intervals and class indices of that busy period's jobs so far, possibly randomized — in the sense that
--   $$\hat W_i = \lim_{n\to\infty}\mathbb E\big(w_i^{(n)}\big), \quad i = 1,\dots,M,$$
--   if and only if $\hat W \in H$, i.e. $\hat W = \sum_{m=1}^M \alpha_m P_m$ for some $M$ performance vectors $P_m$ of preemptive priority disciplines and weights $\alpha_m \ge 0$ with $\sum_m \alpha_m = 1$.
--
--   The theorem identifies the set of achievable mean response-time vectors with the convex hull of the $M!$ preemptive priority vectors; every achievable vector is realized by mixing priority disciplines busy period by busy period.
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
--   - reading: definition (3) prints α1 + α2 + ··· + αm = 1 → Σ_{m=1}^M αm = 1; reason: the lower-case m is a misprint for M; the M numbers α1, …, αM are the ones summed
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 816, Theorem 2

import Mathlib
import Definitions.Def_CoffmanMitrani_Achievable
import Definitions.Def_CoffmanMitrani_H

namespace CoffmanMitrani

/-- **Theorem 2 (Coffman–Mitrani characterization of achievable response-time vectors).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 816, Theorem 2: "A desired performance vector Ŵ is achievable by some scheduling
strategy if and only if Ŵ ∈ H."

In the multiclass M/M/1 model (`Data`), a vector `W` of mean response times is achieved by some
scheduling strategy satisfying Assumptions 1–3 (`IsStrategy`, `Achieves`) if and only if `W` is a
convex combination of `M` of the performance vectors of the preemptive priority disciplines
(definition (3), `H`).

**Formalization Note.** Classes `Fin M` (0-based); priority order `σ` with `σ 0` highest; strategies
are schedules on a canonical product space, randomized through per-job seeds, with decisions in a
busy period depending only on that busy period's arrival, schedule and departure record and the
seeds of its opening job (`IsStrategy`, clause 5). -/
theorem theorem_2 (D : Data) (W : Fin D.M → ℝ) :
    Achievable D W ↔ W ∈ H D := by sorry

end CoffmanMitrani
