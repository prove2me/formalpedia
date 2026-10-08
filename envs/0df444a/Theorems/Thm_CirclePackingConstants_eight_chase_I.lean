-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_chase_I
-- name    : CirclePackingConstants.eight_chase_I
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T10:18:42.551383+00:00
-- url     : https://prove2.me/theorems/6bf4418f-984a-4e0e-8ea8-d4cf6be64ff3
-- title:
--   Schaer–Meir, steps (ii)–(iii): the top-arm point lies in $CN_2R_2H_2$
-- statement:
--   Use coordinates centred at the centre of the unit square, $s=(2-\sqrt3)/2$, $d_8=\sqrt{2-\sqrt3}$, the closed cells $\sigma_1,\dots,\sigma_8$ of `eightCell` and the quadrilateral $CN_2R_2H_2$ of `eightQuad`. Let $p_0\in\sigma_1$ (the corner square at $A_1$), $p_1\in\sigma_2$ (the top arm), $p_2\in\sigma_3$ (the corner square at $A_2$) and $p_7\in\sigma_8$ (the right arm) be four points with
--
--   $$|p_0-p_1|>d_8,\quad |p_1-p_2|>d_8,\quad |p_0-p_7|>d_8,\quad |p_1-p_7|>d_8,$$
--
--   and suppose $p_7=(u,v)$ lies in the closed trapezium $B_1D_1L_1K_1$, i.e. $v\ge0$ and $u+v\ge\tfrac12-s$. Then $p_1$ lies in the quadrilateral $C\,N_2\,R_2\,H_2$.
--
--   This is steps (ii) and (iii) of the proof of Proposition 3 of Schaer and Meir: the position of $p_7$ forces $p_0$ into the triangle $G_1E_1O_1$, hence $p_1$ outside the polygon $G_1D_2O_2N_2H_1O_1$, and then, with $p_2$ and $p_7$, into $CN_2R_2H_2$.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Proposition 3, steps (ii) and (iii), with the Lemma, Figure 3.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Definitions.Def_CirclePackingConstants_EightQuad

noncomputable section

namespace CirclePackingConstants

theorem eight_chase_I (p0 p1 p2 p7 : Point) (h0 : eightCell 0 p0) (h1 : eightCell 1 p1)
    (h2 : eightCell 2 p2) (h7 : eightCell 7 p7)
    (hT : 0 ≤ p7.2 ∧ 1 / 2 - eightS ≤ p7.1 + p7.2)
    (d01 : 2 - Real.sqrt 3 < sqDist p0 p1) (d12 : 2 - Real.sqrt 3 < sqDist p1 p2)
    (d07 : 2 - Real.sqrt 3 < sqDist p0 p7) (d17 : 2 - Real.sqrt 3 < sqDist p1 p7) :
    eightQuad p1 := by sorry
