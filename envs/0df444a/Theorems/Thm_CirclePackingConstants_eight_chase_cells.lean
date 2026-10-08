-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_chase_cells
-- name    : CirclePackingConstants.eight_chase_cells
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T09:09:15.732921+00:00
-- url     : https://prove2.me/theorems/e961b837-0af3-4c00-b250-c5ae56e64224
-- title:
--   Schaer–Meir: no eight-point configuration with an arm point outside $K_1K_2K_3K_4$
-- statement:
--   Use Cartesian coordinates $(u,v)$ centred at the centre of the unit square (so the square is $[-\tfrac12,\tfrac12]^2$), put $s=(2-\sqrt3)/2$ and $d_8=\sqrt{2-\sqrt3}$, and let $\sigma_1,\dots,\sigma_8$ be the eight closed cells of Schaer and Meir (four corner squares $[s,\tfrac12]^2$ and its rotations, and four pentagons around the arms of the central cross; see `eightCell`). Index the points $p_0,\dots,p_7$ so that $p_{i}\in\sigma_{i+1}$; the cell $\sigma_8$ is the right arm $\{|v|\le s,\ |v|\le u\le\tfrac12\}$.
--
--   Assume $p_0,\dots,p_7$ are pairwise at distance greater than $d_8$, and the point $p_7=(u,v)$ of the right arm satisfies $$v\ge 0,\qquad u+v\ge \tfrac12-s ,$$ i.e. it lies in the closed trapezium $B_1D_1L_1K_1$ of Schaer and Meir, outside the open square $K_1K_2K_3K_4$. Then we obtain a contradiction:
--
--   $$\text{such a configuration does not exist.}$$
--
--   This is the main argument (steps (i)–(v) of the proof of Proposition 3) of Schaer and Meir, in the form needed for eight points: it shows that a point of an arm cannot lie outside $K_1K_2K_3K_4$.
--
--   **Formalization Note.** `eightCell i` and `eightS` are defined in `CirclePackingConstants_Eight`; the cells are closed.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Propositions 2 and 3 (steps (i)-(v) of the proof of Proposition 3) with the Lemma, Figure 3.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight

noncomputable section

namespace CirclePackingConstants

theorem eight_chase_cells (p : Fin 8 → Point) (hc : ∀ i, eightCell i (p i))
    (hT : 0 ≤ (p 7).2 ∧ 1 / 2 - eightS ≤ (p 7).1 + (p 7).2)
    (hd : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) : False := by sorry
