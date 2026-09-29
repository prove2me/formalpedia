-- Prove2me | Theorems.Thm_AGT_male_optimal_exists
-- name    : AGT.male_optimal_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:11:03.148375+00:00
-- url     : https://prove2.me/theorems/cb2895c9-cd4c-4f56-8fd4-f76b774c3156
-- title:
--   A male-optimal stable matching exists
-- statement:
--   Some stable matching is weakly best for every man simultaneously — Gale–Shapley's optimal assignment (1962, Theorem 2). In every finite marriage market with strict preferences and $|M| = |W|$ there is a stable $\mu$ such that for every stable $\nu$ and every man $m$, either $\mu(m) = \nu(m)$ or $m$ strictly prefers $\mu(m)$ to $\nu(m)$.
--
--   *A note on the rendering and the attribution.* Theorem 10.11 of *Algorithmic Game Theory* states the male-optimality of the Deferred Acceptance outcome in the book's own, weaker form: no stable alternative makes every man weakly and some man strictly better off (p. 257). The man-by-man form asserted here is Gale–Shapley's original notion and implies the book's outright; conversely, for finite strict markets any Pareto-undominated stable matching coincides with the man-by-man optimum (which exists), so the two definitions carve out the same matchings — but that equivalence is a theorem, which is why this statement is attributed to Gale–Shapley 1962 and only rendered *from* the book's Theorem 10.11. With strict preferences the male-optimal stable matching is unique — two of them would be weakly preferred to each other by every man — which is what lets the capstone speak of *the* male-optimal mechanism. This statement is deliberately freed of the algorithm; any construction of Deferred Acceptance proves it.
-- source:
--   D. Gale, L. S. Shapley, College admissions and the stability of marriage, Amer. Math. Monthly 69 (1962), Theorem 2, https://doi.org/10.2307/2312726; rendered from N. Nisan et al. (eds.), Algorithmic Game Theory, CUP 2007, Section 10.4.1, Theorem 10.11, p. 257 (the book states the equivalent no-Pareto-improvement form)

import Definitions.Def_agt_matching

namespace AGT

/-- A male-optimal stable matching exists: there is a stable matching that
every man weakly prefers to every other stable matching — the male-propose
Deferred Acceptance outcome.  The man-by-man form of optimality asserted
here is Gale–Shapley's (1962, Theorem 2); Theorem 10.11 of *Algorithmic
Game Theory* states the equivalent no-Pareto-improvement form — no stable
alternative makes every man weakly and some man strictly better off —
which this statement implies outright and, for finite strict markets,
also follows from (any Pareto-undominated stable matching coincides with
the man-by-man optimum). -/
theorem male_optimal_exists {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : IsPrefProfile PM) (hW : IsPrefProfile PW)
    (hcard : Nonempty (M ≃ W)) :
    ∃ μ : M ≃ W, IsMaleOptimal PM PW μ := by
  sorry

end AGT
