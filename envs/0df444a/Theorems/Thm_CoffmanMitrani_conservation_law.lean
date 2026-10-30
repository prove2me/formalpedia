-- Prove2me | Theorems.Thm_CoffmanMitrani_conservation_law
-- name    : CoffmanMitrani.conservation_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:23:00.581119+00:00
-- url     : https://prove2.me/theorems/c405f050-546f-4907-ac16-064dfa02081c
-- title:
--   Kleinrock's conservation law (1)
-- statement:
--   For every scheduling strategy $S$ satisfying the paper's assumptions and achieving the performance vector $W = (W_1,\dots,W_M)$,
--   $$\sum_{i=1}^M \rho_i W_i = \frac{V}{1-\rho}, \qquad V = \sum_{i=1}^M \frac{\lambda_i}{\mu_i^2}.$$
--
--   The weighted sum of the mean response times is the same for all scheduling strategies; this is a necessary condition for a vector to be achievable.
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
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 813, eq. (1)

import Mathlib
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_Data_rho
import Definitions.Def_CoffmanMitrani_Data_V

namespace CoffmanMitrani

/-- **Kleinrock's conservation law (1).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 813, eq. (1): "Finally, for any strategy satisfying Assumptions 1 and 2, the following
relation holds: Σ_{i=1}^M ρi Wi = V/(1 − ρ) where V = Σ_{i=1}^M (λi/μi²). (1)"

If `S` is a scheduling strategy achieving the performance vector `W`, then
`Σ_i ρi Wi = V / (1 − Σ_i ρi)`.

**Formalization Note.** "Strategy satisfying Assumptions 1 and 2" is `IsStrategy` (Assumptions
1–3); `Wi` exists by `Achieves`. Classes are `Fin M` (0-based). -/
theorem conservation_law (D : Data) (S : Schedule D.M) (W : Fin D.M → ℝ)
    (hS : IsStrategy D S) (hW : Achieves D S W) :
    ∑ i, D.rho i * W i = D.V / (1 - ∑ i, D.rho i) := by sorry

end CoffmanMitrani
