-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_four_points_in_diamond
-- name    : CirclePackingConstants.eight_four_points_in_diamond
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T06:36:26.927886+00:00
-- url     : https://prove2.me/theorems/10b0570a-5cf1-4f68-8165-869e61152f29
-- title:
--   Eight points of the unit square with pairwise distance $>d_8$ have four points in $K_1K_2K_3K_4$
-- statement:
--   Let $p_0,\dots,p_7$ be eight points of the closed unit square $[0,1]^2$ whose pairwise squared distances all exceed $2-\sqrt3$, that is, whose pairwise distances all exceed $d_8=\sqrt{2-\sqrt3}=(\sqrt6-\sqrt2)/2$. Let
--
--   $$
--   \Diamond=\Big\{(x,y):\ \big|x-\tfrac12\big|+\big|y-\tfrac12\big|\le \tfrac{\sqrt3-1}{2}\Big\}
--   $$
--
--   be the closed square, centred at the centre of the unit square and rotated by $45^\circ$, with vertices $K_1=(1-s,\tfrac12)$, $K_2=(\tfrac12,1-s)$, $K_3=(s,\tfrac12)$, $K_4=(\tfrac12,s)$, where $s=(2-\sqrt3)/2$; its side length is $d_8$. Then four of the points, with four distinct indices $i_0,i_1,i_2,i_3$, lie in $\Diamond$.
--
--   This is Proposition 3 of Schaer and Meir (1965), the main step of their proof of Moser's conjecture for eight points: together with the elementary fact that four points of a square of side $d_8$ contain two at distance at most $d_8$, it shows that eight points of the unit square always contain two at distance at most $d_8$.
--
--   **Formalization Note.** The conclusion is an injective map `q : Fin 4 → Fin 8` with `p (q k) ∈ ◇` for all `k`; the closed diamond is written with absolute values.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Propositions 3-4 (Figures 2(b) and 3). Eight-point case of Moser's conjecture.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem eight_four_points_in_diamond : ∀ p : Fin 8 → Point,
    (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
    (∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) →
    ∃ q : Fin 4 → Fin 8, Function.Injective q ∧
      ∀ k, |(p (q k)).1 - 1 / 2| + |(p (q k)).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2 := by sorry
