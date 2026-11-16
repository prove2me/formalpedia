-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_theorem_5
-- name    : CorrKClust.BalancedPivot.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:46.903341+00:00
-- url     : https://prove2.me/theorems/29aeb6f2-e10b-4fa8-b8e8-2344bc7a034e
-- title:
--   Theorem 5 — expected competitiveness of UNIFORM PIVOT
-- statement:
--   There is an absolute constant $C>0$ such that, for every disjoint-clique graph $G$ on any finite number $n$ of vertices and every $k\ge1$, UNIFORM PIVOT satisfies
--   $$\mathbb E_{\sigma,\mathrm{coins}}[\operatorname{Cost}_G]\le C(\log_2n)^3\operatorname{OPT}_k(G).$$
--   The arrival permutation is uniform and, conditionally on it, each later pivot independently chooses uniformly from $S$ frozen at the $k$th pivot. The fixed threshold for $S$ is $128\ln n$. The final statement includes the zero-cost cases $n\le1$ and $\ell\le k$ and has no additive term. This companion theorem gives the stronger exponent available for disjoint cliques.
--
--   Differences from the source:
--   - encoding: a suitably chosen constant c0 in UNIFORM PIVOT → c0=128 ln 2, so the frozen threshold is exactly 128 ln n; reason: printed p.28 chooses c=32 in Lemma 6.2 and 4c ln n=c0 log₂n
--   - encoding: expectation over the random order and the algorithm choices → a uniform order average of the conditional product law on the frozen S; reason: the choice law is independent across pivots conditional on the order; the empty and singleton cases incur zero cost
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Theorem 5, p. 22

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Uniform

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Theorem 5, printed p.22 (repeated p.24). Includes all n and k≥1 with no additive term.
The fixed threshold is 128 ln n = (128 ln 2) log₂ n. -/
theorem theorem_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (hk : 0 < k)
      (G : SimpleGraph (Fin n)) (Q : Fin n → Fin n), IsCliquePartition G Q →
      uniformCost hk G ≤ C * (logTwo n) ^ 3 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot.Supplement
