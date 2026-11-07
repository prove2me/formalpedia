-- Prove2me | Theorems.Thm_EuclidSPAgg_proposition_5_2
-- name    : EuclidSPAgg.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:11.008194+00:00
-- url     : https://prove2.me/theorems/9502eb27-5fcf-4591-a965-059e505fe168
-- title:
--   Proposition 5.2 — if the absorber is a fixed-rank rule in a frame $\mathcal B$, the original mechanism uses the same frame with every rank raised by one
-- statement:
--   Let $N\ge4$ and let $f:E^N\to E$ be anonymous, continuous and strategyproof. Suppose $g:E^{N-2}\to E$ satisfies the absorbing identity $f(a,g(z),z)=g(z)$, and that in one fixed orthonormal frame $\mathcal B$, $g=Q_{\mathcal B,k}$ with ranks $1\le k_j\le N-2$, i.e. $g_j(z)=z_{(k_j),j}$ for every $z$ and every coordinate $j$. Then, in the same frame,
--   $$
--   f_j(x)=x_{(k_j+1),j}\qquad\text{for every profile }x\text{ and every coordinate }j,
--   $$
--   that is, $f=Q_{\mathcal B,k+1}$.
--
--   This is the rank-lifting step that carries the classification from $N-2$ reports to $N$ reports.
--
--   **Formalization Note** $N=M+2$ with $M\ge2$, and ranks are $0$-based; the lifted rank index is the old index plus one. No compactness hypothesis is assumed.
--
--   Differences from the source:
--   - encoding: g_j(z) = z_{(k_j),j} for all z and j, 1 ≤ k_j ≤ N − 2 → g = Q B k with k : Fin d → Fin M; reason: a vector is determined by its B-coordinates; 0-based ranks in Fin M are exactly the ranks 1, …, N − 2
--   - encoding: f_j(x) = x_{(k_j+1),j} → f = Q B (fun j => (k j).succ.castSucc); reason: the index (k j).succ.castSucc has value k j + 1, the 0-based form of rank k_j + 1
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Proposition 5.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_Q
import Definitions.Def_EuclidSPAgg_Absorbs
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Proposition 5.2** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.25 (PDF p.27)). Let `N ≥ 4`, and let `f : E^N → E` be anonymous,
continuous and strategyproof. Suppose that `g : E^{N−2} → E` is an absorber satisfying (3.1), and
that in one fixed frame `B`, `g_j(z) = z_{(k_j),j}` for `1 ≤ k_j ≤ N − 2`. Then, in the same frame,
`f_j(x) = x_{(k_j+1),j}` for every profile `x` and every coordinate `j`.

**Formalization Note** `N = M + 2` with `M ≥ 2`. The coordinate formula for `g` in frame `B` for
all `j` and `z` is `g = Q B k`; ranks are 0-based (`k : Fin d → Fin M` covers exactly
`1 ≤ k_j ≤ N − 2`), and the lifted rank `k_j + 1` is the index `(k j).succ.castSucc : Fin (M + 2)`,
of value `k j + 1`. No compactness hypothesis is printed and none is added. `d ≥ 1` is standing
(p.8). -/
theorem proposition_5_2 (M d : ℕ) (hM : 2 ≤ M) (hd : 1 ≤ d) (f : Mech (M + 2) d)
    (hA : IsAnonymous f) (hC : Continuous f) (hSP : IsStrategyproof f)
    (g : Mech M d) (hg : Absorbs f g) (B : OrthonormalBasis (Fin d) ℝ (E d))
    (k : Fin d → Fin M) (hgQ : g = Q B k) :
    f = Q B (fun j => (k j).succ.castSucc) := by sorry

end EuclidSPAgg
