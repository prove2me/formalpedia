-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_4_8
-- name    : ChengCapClustering.Soft.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:53:09.848338+00:00
-- url     : https://prove2.me/theorems/2d9f1405-fd02-4413-8b29-6d4f183f1889
-- title:
--   Lemma 4.8 — routes: network paths never underestimate $\mathrm{dist}^z$, and good pairs have a path of cost $\le((1+8\lambda\Lambda)\mathrm{dist})^z$
-- statement:
--   Let $X$ (doubling dimension at most $D$, minimum distance $2$) carry a hierarchical decomposition $D$, portals with spacing $\lambda\in(0,1]$ and parents as in §4.3.1, and let $z\ge1$. For $x,y\in X$: (a) every path from $x_{src}$ to $y_{snk}$ in $N_D$ has cost at least $\mathrm{dist}(x,y)^z$; (b) for $\Lambda\ge1$, if $x=y$ or $(x,y)$ is not $\Lambda$-bad, some path from $x_{src}$ to $y_{snk}$ has cost at most $((1+8\lambda\Lambda)\,\mathrm{dist}(x,y))^z$.
--
--   Differences from the source:
--   - encoding: the network N_D with fixed maximal portal sets and fixed parent portals → the network of any valid portal system (maximal λ2^h-separated portal sets, parents within λ2^{h+1}) given as data; reason: the source fixes an arbitrary such choice; the statement holds for each
--   - encoding: paths of N_D → nonempty vertex lists from src x to snk y with an arc between consecutive vertices; cost = sum of arc costs; reason: N_D is acyclic, so walks are paths
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 4.8, printed pp. 17–18 / PDF pp. 19–20

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Network

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Lemma 4.8 (Routes), printed pp. 17–18 / PDF pp. 19–20. In the network `N_D` of a hierarchical
decomposition with a valid portal system (spacing `λ ∈ (0, 1]`), for points `x, y ∈ X`:
(a) every path from `x_src` to `y_snk` costs at least `dist(x, y)^z`;
(b) for `Λ ≥ 1`, if `x = y` or `(x, y)` is not `Λ`-bad, some path from `x_src` to `y_snk` costs at
most `((1 + 8λΛ) dist(x, y))^z`. -/
theorem lemma_4_8 (V : Type u) [MetricSpace V] (D z lam : ℝ) (N : ℕ) (x : Fin N → V)
    (hx : Function.Injective x) (hD : IsDoublingWith (Set.range x) D) (hmin : MinDistTwo x)
    (hz : 1 ≤ z) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (Dec : HierDecomp N)
    (hDec : Dec.IsValid x) (P : PortalSystem N Dec.H) (hP : P.IsValid x Dec lam)
    (i j : Fin N) :
    (∀ path : List (NetVertex N Dec.H), IsNetPath Dec P path (.src i) (.snk j) →
      dist (x i) (x j) ^ z ≤ pathCost x z lam path) ∧
    ∀ Λ : ℝ, 1 ≤ Λ → (i = j ∨ ¬ Dec.IsBad x Λ i j) →
      ∃ path : List (NetVertex N Dec.H), IsNetPath Dec P path (.src i) (.snk j) ∧
        pathCost x z lam path ≤ ((1 + 8 * lam * Λ) * dist (x i) (x j)) ^ z := by sorry

end ChengCapClustering.Soft
