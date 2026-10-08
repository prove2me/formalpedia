-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_JN_decomp
-- name    : ArapostathisAC.CanonicalPolicy.JN_decomp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:42:09.737722+00:00
-- url     : https://prove2.me/theorems/1f643194-a198-43b6-8ff9-41880ed3bc2e
-- title:
--   p. 319 — J_N(x, π, h) = J_N(x, π) + E^π_x[h(X_N)] for bounded c and h
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and one-stage cost bounded on the set $K$ of admissible state–action pairs, and let $h \in \mathcal M_b(S)$ be a bounded measurable terminal cost. Then for every admissible policy $\pi \in \Pi$, every horizon $N \in \mathbb N_0$ and every initial state $x \in S$,
--   $$J_N(x, \pi, h) = J_N(x, \pi) + E^\pi_x[h(X_N)].$$
--
--   The paper uses this identity for $\pi^*$ on p. 319 and, implicitly, for an arbitrary $\pi$ in the "Hence" step on p. 318. It separates the terminal cost from the running cost, which is what turns the $N$-stage optimality of a canonical policy into a bound on $J_N(x, \pi^*)$ itself.
--
--   **Formalization Note.** The paper states the identity for $\pi^*$; it is stated here for every $\pi \in \Pi$, which is how the proof of Theorem 6.3 (i) applies it. Both expectations are Bochner integrals; boundedness of $c$ on $K$ and of $h$ is what makes them genuine (the trajectory lies in $K$ almost surely because every policy is admissible).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 319, proof of Theorem 6.3, "since J_N(x, π*, h) = J_N(x, π*) + E^{π*}_x[h(X_N)]"

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- p. 319 (and p. 318): for `c ∈ 𝓜_b(K)` and `h ∈ 𝓜_b(S)`, the `N`-stage cost with terminal
cost `h` splits as `J_N(x, π, h) = J_N(x, π) + E^π_x[h(X_N)]`, for every policy `π ∈ Π`. -/
theorem JN_decomp (M : BorelCMP S A) (hc : CostBounded M) (h : S → ℝ) (hh : IsBoundedMeas h)
    (π : Policy M) (N : ℕ) (x : S) :
    JN M π N h x = JN0 M π N x + ∫ ω, h (ω N).1 ∂(pathMeasure M π x) := by sorry

end ArapostathisAC.CanonicalPolicy
