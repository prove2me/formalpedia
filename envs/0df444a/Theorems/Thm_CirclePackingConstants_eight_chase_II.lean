-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_chase_II
-- name    : CirclePackingConstants.eight_chase_II
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T10:18:50.136462+00:00
-- url     : https://prove2.me/theorems/9f9c6f79-1dfb-4a4d-8504-e59f90198b6b
-- title:
--   Schaer–Meir, step (iv): the left-arm point lies in $B_3D_3L_3K_3$
-- statement:
--   With the notation of `eight_chase_I`, let $p_1\in\sigma_2$ (the top arm) lie in the quadrilateral $CN_2R_2H_2$, let $p_3\in\sigma_4$ (the left arm) and $|p_1-p_3|>d_8$. Then $p_3=(u,v)$ lies in the closed trapezium $B_3D_3L_3K_3$, the image of $B_1D_1L_1K_1$ under the point reflection about the centre:
--
--   $$ v\le0,\qquad -u-v\ge \tfrac12-s .$$
--
--   This is step (iv) of the proof of Proposition 3 of Schaer and Meir.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Proposition 3, step (iv), with the Lemma, Figure 3.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Definitions.Def_CirclePackingConstants_EightQuad

noncomputable section

namespace CirclePackingConstants

theorem eight_chase_II (p1 p3 : Point) (h1 : eightCell 1 p1) (h3 : eightCell 3 p3)
    (hq : eightQuad p1) (d13 : 2 - Real.sqrt 3 < sqDist p1 p3) :
    0 ≤ -p3.2 ∧ 1 / 2 - eightS ≤ -p3.1 - p3.2 := by sorry
