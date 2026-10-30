-- Prove2me | Theorems.Thm_CoffmanMitrani_theorem_1_mixing
-- name    : CoffmanMitrani.theorem_1_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:23:52.99586+00:00
-- url     : https://prove2.me/theorems/27b64375-d27d-4baa-9edc-e2baba62f130
-- title:
--   Theorem 1: response time of a mixing strategy
-- statement:
--   Let $S_1,\dots,S_k$ be scheduling strategies with performance vectors $W_1,\dots,W_k$, and let $\alpha_1,\dots,\alpha_k \ge 0$ with $\alpha_1+\dots+\alpha_k = 1$. Then the mixing strategy for $S_1,\dots,S_k$ with these parameters is a scheduling strategy, and its performance vector is
--   $$W = \sum_{j=1}^k \alpha_j W_j. \qquad (2)$$
--
--   The first part is the closure of the class of strategies under mixing, stated on p. 814 before Theorem 1.
--
--   Differences from the source:
--   - encoding: classes 1, …, M and the nth arriving job of class i → classes Fin M and job index n : ℕ, both 0-based; reason: Lean indexing; the same objects
--   - encoding: M classes, Poisson rates λi, exponential parameters μi, equilibrium assumed (ρ < 1) → Data with 1 ≤ M, 0 < λi, 0 < μi and Σ λi/μi < 1; reason: the rates of a Poisson stream and of an exponential law are positive, M = 0 has no classes, and ρ < 1 is the paper's standing equilibrium assumption (pp. 812–813)
--   - encoding: Poisson arrivals and exponential services, mutually independent; randomized strategies governed by some probability law (Assumption 3) → canonical product space of exponential interarrival times, exponential service requirements and i.i.d. uniform seed sequences per job; a randomized strategy is a function of the seeds of the job that opens the current busy period; reason: every randomized decision law can be generated from i.i.d. uniform seeds; one seed sequence per busy period keeps busy periods independent
--   - reading: Assumptions 2–3: S(t) restricted to arrival times, departure times, execution intervals and class indices of the jobs of the current busy period B up to time t, and no information from prior busy periods → IsStrategy clause 5: S(t) = rule(record of the current busy period up to t, with relative times and within-busy-period ranks; that busy period's seeds), one rule for all busy periods; reason: formal content of 'the domain of S(t) is restricted to'; it excludes service requirements not yet revealed, future arrivals, absolute time and the busy-period count
--   - encoding: S(t) a random mapping; Assumption 1 (no idling iff idle period); jobs eventually served → joint null-measurability of S, and clauses 2–4 of IsStrategy required almost surely, including a completion clause; reason: measurability is needed for wi(n) to be a random variable; completion follows almost surely from Assumption 1 and ρ < 1, and makes departure times well defined
--   - encoding: busy and idle periods defined through the presence of jobs requiring service → busy periods defined from the arrival and service data (IsBPStart, InBP); reason: under Assumption 1 the busy periods are the same for every strategy (p. 813)
--   - encoding: Wi = lim_{n→∞} E(wi(n)), whose existence is assumed → every wi(n) integrable and E(wi(n)) → Wi; reason: rules out the junk value ∫ = 0 of a non-integrable function; under ρ < 1 response times of strategies are integrable
--   - encoding: k strategies with parameters α1, …, αk−1 and αk = 1 − α1 − ··· − αk−1 → K + 1 strategies indexed by Fin (K + 1) and a probability vector α (α j ≥ 0, Σ α j = 1); reason: the same parameter sets
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, p. 814, Theorem 1

import Mathlib
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_mix

namespace CoffmanMitrani

/-- **Theorem 1 (mixing).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, p. 814, Theorem 1: "The response time vector of the mixing strategy for S1, S2, ···, Sk
with parameters α1, α2, ···, αk−1 is given by W = Σ_{i=1}^k αi Wi (2) where
αk = 1 − α1 − α2 − ··· − αk−1." and, before it: "Note that the class of strategies that we have
defined is closed under the mixing operation."

For scheduling strategies `S 0, …, S K` achieving `Wv 0, …, Wv K` and a probability vector `α`, the
mixing strategy `mix α S` is a scheduling strategy and achieves `Σ_j α j • Wv j`.

**Formalization Note.** `k = K + 1` strategies indexed by `Fin (K + 1)` (0-based); the parameters
are the probability vector `α` (`α j ≥ 0`, `Σ α j = 1`), equivalent to the paper's free parameters
with `αk = 1 − α1 − ··· − αk−1`. -/
theorem theorem_1_mixing (D : Data) {K : ℕ} (S : Fin (K + 1) → Schedule D.M)
    (Wv : Fin (K + 1) → Fin D.M → ℝ) (α : Fin (K + 1) → ℝ)
    (hS : ∀ j, IsStrategy D (S j)) (hW : ∀ j, Achieves D (S j) (Wv j))
    (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1) :
    IsStrategy D (mix α S) ∧ Achieves D (mix α S) (∑ j, α j • Wv j) := by sorry

end CoffmanMitrani
