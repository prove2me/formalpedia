-- Prove2me | Theorems.Thm_CoffmanMitrani_achievable_iff_Hss
-- name    : CoffmanMitrani.achievable_iff_Hss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:33:43.002001+00:00
-- url     : https://prove2.me/theorems/5c0985c4-b330-4caa-8b19-3caa958b554c
-- title:
--   $H^* = H^{**}$: analytical characterization of achievability
-- statement:
--   A performance vector $\hat W$ is achievable by some scheduling strategy if and only if it satisfies the conservation law (1) and the $2^M - 2$ inequalities (4):
--   $$H^* = H^{**}.$$
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
--   - encoding: Poisson arrivals and exponential services, mutually independent; randomized strategies governed by some probability law (Assumption 3) → canonical product space of exponential interarrival times, exponential service requirements and i.i.d. uniform seed sequences per job; a randomized strategy is a function of the seeds of the job that opens the current busy period; reason: every randomized decision law can be generated from i.i.d. uniform seeds; one seed sequence per busy period keeps busy periods independent
--   - reading: Assumptions 2–3: S(t) restricted to arrival times, departure times, execution intervals and class indices of the jobs of the current busy period B up to time t, and no information from prior busy periods → IsStrategy clause 5: S(t) = rule(record of the current busy period up to t, with relative times and within-busy-period ranks; that busy period's seeds), one rule for all busy periods; reason: formal content of 'the domain of S(t) is restricted to'; it excludes service requirements not yet revealed, future arrivals, absolute time and the busy-period count
--   - encoding: S(t) a random mapping; Assumption 1 (no idling iff idle period); jobs eventually served → joint null-measurability of S, and clauses 2–4 of IsStrategy required almost surely, including a completion clause; reason: measurability is needed for wi(n) to be a random variable; completion follows almost surely from Assumption 1 and ρ < 1, and makes departure times well defined
--   - encoding: busy and idle periods defined through the presence of jobs requiring service → busy periods defined from the arrival and service data (IsBPStart, InBP); reason: under Assumption 1 the busy periods are the same for every strategy (p. 813)
--   - encoding: Wi = lim_{n→∞} E(wi(n)), whose existence is assumed → every wi(n) integrable and E(wi(n)) → Wi; reason: rules out the junk value ∫ = 0 of a non-integrable function; under ρ < 1 response times of strategies are integrable
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818

import Mathlib
import Definitions.Def_CoffmanMitrani_Achievable
import Definitions.Def_CoffmanMitrani_Hss

namespace CoffmanMitrani

/-- **`H* = H**`: the analytical characterization.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818: "The equation H* = H** provides us with an analytical characterization of H*. To
determine whether a performance requirement Ŵ is achievable or not, it suffices to verify whether it
satisfies (1) and the 2^M − 2 inequalities (4)."

A performance vector is achievable by some scheduling strategy if and only if it satisfies the
conservation law (1) and the inequalities (4) for all nonempty proper sets of classes. -/
theorem achievable_iff_Hss (D : Data) (W : Fin D.M → ℝ) :
    Achievable D W ↔ W ∈ Hss D := by sorry

end CoffmanMitrani
