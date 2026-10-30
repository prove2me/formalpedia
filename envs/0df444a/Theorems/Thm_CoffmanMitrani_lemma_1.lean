-- Prove2me | Theorems.Thm_CoffmanMitrani_lemma_1
-- name    : CoffmanMitrani.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:05.942871+00:00
-- url     : https://prove2.me/theorems/c8263b1f-b3cd-4e85-91b9-dedc20780909
-- title:
--   Lemma 1: the inequalities (4)
-- statement:
--   Every achievable performance vector $W = (W_1,\dots,W_M)$ satisfies
--   $$\sum_{i\in g}\rho_i W_i \ \ge\ \frac{\sum_{i\in g}\rho_i/\mu_i}{1-\sum_{i\in g}\rho_i} \qquad (4)$$
--   for every nonempty set $g$ of classes. For $g = \{1,\dots,M\}$, (4) holds with equality and is the conservation law.
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
--   - encoding: Poisson arrivals and exponential services, mutually independent; randomized strategies governed by some probability law (Assumption 3) → canonical product space of exponential interarrival times, exponential service requirements and i.i.d. uniform seed sequences per job; a randomized strategy is a function of the seeds of the job that opens the current busy period; reason: every randomized decision law can be generated from i.i.d. uniform seeds; one seed sequence per busy period keeps busy periods independent
--   - reading: Assumptions 2–3: S(t) restricted to arrival times, departure times, execution intervals and class indices of the jobs of the current busy period B up to time t, and no information from prior busy periods → IsStrategy clause 5: S(t) = rule(record of the current busy period up to t, with relative times and within-busy-period ranks; that busy period's seeds), one rule for all busy periods; reason: formal content of 'the domain of S(t) is restricted to'; it excludes service requirements not yet revealed, future arrivals, absolute time and the busy-period count
--   - encoding: S(t) a random mapping; Assumption 1 (no idling iff idle period); jobs eventually served → joint null-measurability of S, and clauses 2–4 of IsStrategy required almost surely, including a completion clause; reason: measurability is needed for wi(n) to be a random variable; completion follows almost surely from Assumption 1 and ρ < 1, and makes departure times well defined
--   - encoding: busy and idle periods defined through the presence of jobs requiring service → busy periods defined from the arrival and service data (IsBPStart, InBP); reason: under Assumption 1 the busy periods are the same for every strategy (p. 813)
--   - encoding: Wi = lim_{n→∞} E(wi(n)), whose existence is assumed → every wi(n) integrable and E(wi(n)) → Wi; reason: rules out the junk value ∫ = 0 of a non-integrable function; under ρ < 1 response times of strategies are integrable
--   - reading: g ⊂ {1, 2, ···, M}, g ≠ φ, with the remark that g = {1, 2, ···, M} gives the conservation law → every nonempty Finset g, including the set of all classes; reason: the paper's ⊂ includes the full set, as its parenthetical remark shows
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, pp. 816–817, Lemma 1

import Mathlib
import Definitions.Def_CoffmanMitrani_Achievable
import Definitions.Def_CoffmanMitrani_Data_loadBound

namespace CoffmanMitrani

/-- **Lemma 1.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, pp. 816–817, Lemma 1: "Every achievable performance vector W = (W1, W2, ···, WM) satisfies
the inequalities Σ_{i∈g} ρi Wi ≥ (Σ_{i∈g} ρi/μi)/(1 − Σ_{i∈g} ρi); g ⊂ {1, 2, ···, M}, g ≠ φ (4)
(if g = {1, 2, ···, M} then (4) is, of course, satisfied with equality; that is, (4) becomes the
conservation law)."

If `W` is achievable then `Σ_{i∈g} ρi Wi ≥ (Σ_{i∈g} ρi/μi)/(1 − Σ_{i∈g} ρi)` for every nonempty set
`g` of classes (including the set of all classes).

**Formalization Note.** The paper's `⊂` includes `g = {1, …, M}`, as its parenthetical remark shows;
the equality in that case is `conservation_law`. -/
theorem lemma_1 (D : Data) (W : Fin D.M → ℝ) (hW : Achievable D W)
    (g : Finset (Fin D.M)) (hg : g.Nonempty) :
    D.loadBound g ≤ ∑ i ∈ g, D.rho i * W i := by sorry

end CoffmanMitrani
