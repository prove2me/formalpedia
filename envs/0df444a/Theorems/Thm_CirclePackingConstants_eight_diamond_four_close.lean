-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_diamond_four_close
-- name    : CirclePackingConstants.eight_diamond_four_close
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T06:36:18.962098+00:00
-- url     : https://prove2.me/theorems/c4a26167-048e-48db-8663-848bdf73a505
-- title:
--   Four points in the square $K_1K_2K_3K_4$ of side $d_8$ contain a pair at distance $\le d_8$
-- statement:
--   Let $\rho=(\sqrt3-1)/2$ and let $\Diamond=\{(x,y): |x-\tfrac12|+|y-\tfrac12|\le\rho\}$ be the closed square, centred at the centre of the unit square and rotated by $45^\circ$, with vertices $K_1=(1-s,\tfrac12)$, $K_2=(\tfrac12,1-s)$, $K_3=(s,\tfrac12)$, $K_4=(\tfrac12,s)$, where $s=(2-\sqrt3)/2$. Its side length is $\sqrt2\,\rho=\sqrt{2-\sqrt3}=d_8$. Then any four points $p_0,\dots,p_3\in\Diamond$ contain two distinct indices $i\ne j$ with $|p_i-p_j|^2\le 2-\sqrt3$.
--
--   This is the four-point case of the best-location problem in a square (Schaer-Meir, Figure 2(b)): four points in a square of side $a$ cannot all be pairwise more than $a$ apart. In the eight-point argument it is the last step: once four of the eight points are known to lie in $\Diamond$, they contain a pair at distance at most $d_8$.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Propositions 3-4 (Figures 2(b) and 3). Eight-point case of Moser's conjecture.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem eight_diamond_four_close : ∀ p : Fin 4 → Point,
    (∀ i, |(p i).1 - 1 / 2| + |(p i).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2) →
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ 2 - Real.sqrt 3 := by sorry
