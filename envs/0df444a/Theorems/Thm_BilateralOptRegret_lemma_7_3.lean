-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_3
-- name    : BilateralOptRegret.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:58.093379+00:00
-- url     : https://prove2.me/theorems/61c50865-85ec-44fc-8c8d-dbd43a74d06e
-- title:
--   Lemma 7.3 (corrected: $K\ge3$) — queryability of reconstruction representatives, with (19)
-- statement:
--   Let $K=2^n+1$, $n\ge1$, and let $v_j$ be built by Algorithm 2 from $G_{\mathrm{tar}}\subseteq G_{\mathrm{qry}}\subseteq\mathcal X_K$. Fix a row $j$ and target points $x_{a,j},x_{b,j}\in G_{\mathrm{tar}}$ with $a<b$. Then
--   $$F(x_{b,j})-F(x_{a,j})=\big(F(x_{b,j})-F(x_{v_j(b),j})\big)+\sum_{(u,w)\in\mathcal B(b,a)}\big(F(x_{v_j(w),j})-F(x_{v_j(u),j})\big)+\big(F(x_{v_j(a),j})-F(x_{a,j})\big),$$
--   and every mapped representative in this decomposition (that of $a$, of $b$, and of each endpoint of a pair of $\mathcal B(b,a)$) belongs to $G_{\mathrm{qry}}$. Consequently every elementary CDF difference it requires can be estimated using only queryable points.
--
--   **Formalization Note** The "consequently" is the membership clause restated: both endpoints of each elementary difference are queryable.
--
--   Differences from the source:
--   - correction: all $K\ge2$ with $K-1$ a power of two → $n\ge1$, i.e. $K\ge3$; reason: at $K=2$, by (9), $\mathcal I^\star=\emptyset$ and boundary indices are fixed, so with $a=0$, $b=1$ and $L=\delta_{(1,0)}$, $j=0$, the right side of (19) is $0$ and the left side is $1$
--   - generalization: (19) for the $v_j$ of Algorithm 2 → (19) for every map $w$; reason: §5.2, p.20, states it for arbitrary maps; the $v_j$ are an instance
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.3, p.29, display (19); §5.2, p.20

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.3** (corrected: `K ≥ 3`), Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.29: queryability of reconstruction representatives.

Let `v_j` come from Algorithm 2 on `G_tar ⊆ G_qry ⊆ X_K`, and let `x_{a,j}, x_{b,j} ∈ G_tar`, `a < b`. Decomposition (19) holds, and each mapped representative in it, that of `a`, of `b`,
and of each endpoint of `B(b, a)`, is in `G_qry`. The printed "consequently" is the membership clause restated: both endpoints of each elementary difference are queryable.

**Formalization Note.** Identity (19) is stated for every map `w`, as §5.2, p.20, has it. `n ≥ 1` because (19) needs Lemma 5.1. `v_j` is `repAfter … (j + 1)`. -/
theorem lemma_7_3 (n : ℕ) (hn : 1 ≤ n) (sel : Finset (Idx n) → Idx n) (hsel : IsSel sel)
    (Gtar Gqry : Finset (Act n)) (hsub : Gtar ⊆ Gqry) (j a b : Idx n) (hab : a < b)
    (ha : (a, j) ∈ Gtar) (hb : (b, j) ∈ Gtar) :
    (∀ (L : Measure (ℝ × ℝ)) (w : Idx n → Idx n),
      F L (pt (Kof n) (b, j)) - F L (pt (Kof n) (a, j)) =
        (F L (pt (Kof n) (b, j)) - F L (pt (Kof n) (w b, j))) +
          ((B n b a).map fun p => F L (pt (Kof n) (w p.2, j)) - F L (pt (Kof n) (w p.1, j))).sum +
          (F L (pt (Kof n) (w a, j)) - F L (pt (Kof n) (a, j)))) ∧
    (repAfter sel Gtar Gqry (j.val + 1) a, j) ∈ Gqry ∧
    (repAfter sel Gtar Gqry (j.val + 1) b, j) ∈ Gqry ∧
    ∀ u ∈ chainPoints (B n b a), (repAfter sel Gtar Gqry (j.val + 1) u, j) ∈ Gqry := by sorry

end BilateralOptRegret
