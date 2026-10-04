-- Prove2me | Theorems.Thm_Aumann1987_TwoPerson_ced_iff_linear_inequalities
-- name    : Aumann1987.TwoPerson.ced_iff_linear_inequalities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:28:13.090435+00:00
-- url     : https://prove2.me/theorems/93e0b19b-4fe6-440f-9e67-20e13af2a2e1
-- title:
--   Proposition 2.3 — a distribution is a c.e.d. iff it satisfies the linear inequalities (2.4), (2.5)
-- statement:
--   Let $G$ be a two-person game with finite action sets $S^1$, $S^2$ and payoffs $h^i_{jk}=h^i(j,k)$ for $j\in S^1$, $k\in S^2$, $i=1,2$. Let $(p_{jk})$ be a distribution: $p_{jk}\ge0$ for all $j,k$ and $\sum_j\sum_k p_{jk}=1$. Then $(p_{jk})$ is a correlated equilibrium distribution — the distribution of a correlated equilibrium (Definition 2.1) on some finite probability space — if and only if
--
--   $$\sum_k\big(h^1_{jk}-h^1_{qk}\big)p_{jk}\ge0\ \ \text{for all }j,q\in S^1\qquad\text{(2.4)}$$
--   and
--   $$\sum_j\big(h^2_{jk}-h^2_{jr}\big)p_{jk}\ge0\ \ \text{for all }k,r\in S^2\qquad\text{(2.5)}.$$
--
--   Thus the correlated equilibrium distributions of a finite two-person game form a compact convex polyhedron in the probability simplex whose defining linear inequalities are written down explicitly; this is the sense in which, as the paper puts it on p. 5, correlated equilibria are computationally simpler objects than Nash equilibria.
--
--   **Formalization Note** The second inequality carries no printed label in the paper; its proof calls it (2.5). "Correlated equilibrium distribution" is the existential notion `IsCED` over finite probability spaces with a genuine probability vector, not the linear inequalities themselves.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 6 (PDF p. 7), Proposition 2.3, (2.4) and (2.5)

import Mathlib
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

namespace Aumann1987.TwoPerson

/-- **Proposition 2.3** (Aumann 1987, p. 6, PDF p. 7). A distribution `(p_{jk})` is a correlated
equilibrium distribution if and only if
(2.4) `∑_k (h¹_{jk} − h¹_{qk}) p_{jk} ≥ 0` for all `j, q` in `S¹`, and
(2.5) `∑_j (h²_{jk} − h²_{jr}) p_{jk} ≥ 0` for all `k, r` in `S²`.

Formalization Note: two players with finite action sets `S¹ = S₁`, `S² = S₂`; `h₁ j k = h¹_{jk}`,
`h₂ j k = h²_{jk}`. "c.e.d." is `IsCED`: the distribution of some correlated equilibrium
(Definition 2.1) on some finite probability space. -/
theorem ced_iff_linear_inequalities {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂] (h₁ h₂ : S₁ → S₂ → ℝ)
    (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    IsCED h₁ h₂ p ↔
      (∀ j q : S₁, 0 ≤ ∑ k, (h₁ j k - h₁ q k) * p j k) ∧
      (∀ k r : S₂, 0 ≤ ∑ j, (h₂ j k - h₂ j r) * p j k) := by sorry

end Aumann1987.TwoPerson
