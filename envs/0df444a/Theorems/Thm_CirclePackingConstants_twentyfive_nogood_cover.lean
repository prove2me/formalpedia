-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_nogood_cover
-- name    : CirclePackingConstants.twentyfive_nogood_cover
-- status  : Proved
-- author  : @kylelyk
-- created : 2026-11-27T06:02:30.708073+00:00
-- url     : https://prove2.me/theorems/a458823d-8fbd-45af-bae4-2629a946f10d
-- title:
--   Every distribution of 25 points over the fifth-cells with an empty cell contains a placed nogood pattern
-- statement:
--   Index the $25$ cells of the $5\times5$ subdivision of the unit square by $c=5i+j$, $0\le i,j\le4$. Let $A$ be a set of cells and $B\subseteq A$, and think of $A$ as the cells that contain at least one point and of $B$ as the cells that contain two points. Assume
--
--   $$|A|+|B|=25\qquad\text{and}\qquad A\ne\{0,\dots,24\},$$
--
--   that is, the count vector with entries in $\{0,1,2\}$ has sum $25$ and at least one entry $0$.
--
--   Then there are a pattern $x=(a,b)$ of the library `Twentyfive.nogoods` (definition `CirclePackingConstants_TwentyfiveNogoods`), a symmetry $k<8$ of the board and a translation $(d_i,d_j)\in\mathbb Z^2$ such that the image of $x$ lies on the board and inside $(A,B)$:
--
--   $$\sigma_{k,d}(a)\subseteq A,\qquad \sigma_{k,d}(b)\subseteq B .$$
--
--   Here $\sigma_{k,d}$ first applies the symmetry coded by $k$ (bit $0$: $i\mapsto4-i$, bit $1$: $j\mapsto4-j$, bit $2$: exchange $i$ and $j$, in this order) and then adds $(d_i,d_j)$ to $(i,j)$.
--
--   This is the combinatorial half of the proof that $25$ points with pairwise distances greater than $1/4$ in the unit square occupy every cell: the library patterns are infeasible (`twentyfive_nogood_batch1`–`twentyfive_nogood_batch6`), and by this theorem every distribution with an empty cell contains one of them. It is a finite statement about subsets of a $5\times5$ board and involves no geometry.
--
--   **Formalization Note** $A$ and $B$ are natural numbers used as $25$-bit masks ($A<2^{25}$, and every bit of $B$ is a bit of $A$); cardinalities are those of the sets of indices $c<25$ whose bit is set; the conclusion is `Twentyfive.PlacedIn x k di dj A B` for some entry `Twentyfive.nogoods[e]? = some x`.
-- source:
--   Original computer-generated decomposition of CirclePackingConstants.twentyfive_missing_cell_halfbox_bound (the occupancy step, §1 of G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 30 (1987) 3–15, https://annalesm.elte.hu/annales30-1987/Annales_1987_T-XXX.pdf). Method after K. J. Nurmela, P. R. J. Östergård, More optimal packings of equal circles in a square, Discrete Comput. Geom. 22 (1999) 439–457, https://doi.org/10.1007/PL00009472, §2.2–2.4 (tile combinations and region elimination), carried out here with exact integer arithmetic. The statement is not quoted from either paper.

import Definitions.Def_CirclePackingConstants_TwentyfiveNogoods

noncomputable section

namespace CirclePackingConstants

theorem twentyfive_nogood_cover (A B : ℕ) (hA : A < 2 ^ 25)
    (hBA : ∀ c, B.testBit c = true → A.testBit c = true)
    (hcard : ((Finset.range 25).filter (fun c => A.testBit c = true)).card +
      ((Finset.range 25).filter (fun c => B.testBit c = true)).card = 25)
    (hz : ∃ c, c < 25 ∧ A.testBit c = false) :
    ∃ (e : ℕ) (x : ℕ × ℕ) (k : ℕ) (di dj : ℤ),
      Twentyfive.nogoods[e]? = some x ∧ k < 8 ∧ Twentyfive.PlacedIn x k di dj A B := by sorry
