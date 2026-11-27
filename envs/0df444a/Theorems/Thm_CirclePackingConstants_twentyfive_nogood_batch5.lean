-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch5
-- name    : CirclePackingConstants.twentyfive_nogood_batch5
-- status  : Proved
-- author  : @kylelyk
-- created : 2026-11-27T06:02:21.523617+00:00
-- url     : https://prove2.me/theorems/33e5eecb-d13b-5219-90c0-439c3b00acba
-- title:
--   Infeasibility of the nogood patterns $604$–$1077$ for 25 points in the unit square
-- statement:
--   Divide the unit square into the $25$ closed cells $Q_c=[i/5,(i+1)/5]\times[j/5,(j+1)/5]$, $c=5i+j$, $0\le i,j\le4$. A cell pattern $(a,b)$ is a pair of sets of cells with $b\subseteq a$; it is *infeasible* if one cannot choose a point $p_{c,0}\in Q_c$ for every $c\in a$ and a second point $p_{c,1}\in Q_c$ for every $c\in b$ such that all chosen points are pairwise more than $1/4$ apart.
--
--   Let $(a_e,b_e)$, $0\le e<1584$, be the patterns of the library `Twentyfive.nogoods` of the definition `CirclePackingConstants_TwentyfiveNogoods`. The theorem states that
--
--   $$(a_e,b_e)\ \text{is infeasible for every}\ 604\le e<1078.$$
--
--   This is batch 5 of 6 of the geometric part of the proof that $25$ points with pairwise distances greater than $1/4$ in the unit square occupy every cell: the batches together say that every library pattern is a forbidden local occupancy pattern, and `twentyfive_nogood_cover` says that every distribution with an empty cell contains one of them.
--
--   **Formalization Note** The entry with index $e$ is addressed as `Twentyfive.nogoods[e]? = some x`; the patterns are $25$-bit masks and `Twentyfive.Infeasible x.1 x.2` quantifies over all families $p:\mathbb N\to\mathbb N\to\mathbb R^2$, of which only the values at the cells of the pattern matter. "More than $1/4$ apart" is $1/16<\mathrm{sqDist}$.
-- source:
--   Original computer-generated decomposition of CirclePackingConstants.twentyfive_missing_cell_halfbox_bound (the occupancy step, §1 of G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 30 (1987) 3–15, https://annalesm.elte.hu/annales30-1987/Annales_1987_T-XXX.pdf). Method after K. J. Nurmela, P. R. J. Östergård, More optimal packings of equal circles in a square, Discrete Comput. Geom. 22 (1999) 439–457, https://doi.org/10.1007/PL00009472, §2.2–2.4 (tile combinations and region elimination), carried out here with exact integer arithmetic. The statement is not quoted from either paper.

import Definitions.Def_CirclePackingConstants_TwentyfiveNogoods

noncomputable section

namespace CirclePackingConstants

theorem twentyfive_nogood_batch5 (e : ℕ) (he1 : 604 ≤ e) (he2 : e < 1078) (x : ℕ × ℕ)
    (hx : Twentyfive.nogoods[e]? = some x) : Twentyfive.Infeasible x.1 x.2 := by sorry
