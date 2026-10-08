-- Prove2me | Theorems.Thm_CirclePackingConstants_sixteen_quarter_cells_struct
-- name    : CirclePackingConstants.sixteen_quarter_cells_struct
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T12:15:37.722907+00:00
-- url     : https://prove2.me/theorems/2cd2abd1-b562-4708-a578-4a23a1db9b02
-- title:
--   Sixteen points, one in each cell of the $4\times4$ subdivision, have a close pair
-- statement:
--   For $i,j\in\{0,1,2,3\}$ let $Q_{ij}=[\tfrac i4,\tfrac{i+1}4]\times[\tfrac j4,\tfrac{j+1}4]$ be the sixteen closed cells of the $4\times4$ subdivision of the unit square, and let $p_{ij}\in Q_{ij}$ be one point in each cell. Then two of the sixteen points are at distance at most $\tfrac13$:
--
--   $$\min_{(i,j)\neq(k,l)}|p_{ij}-p_{kl}|^2\le \tfrac19 .$$
--
--   Equivalently, it is impossible that all pairs satisfy $|p_{ij}-p_{kl}|^2>\tfrac19$. The bound is sharp: the grid $p_{ij}=(\tfrac i3,\tfrac j3)$ lies in the cells and has minimal squared distance exactly $\tfrac19$. A cell has diameter $\sqrt2/4>\tfrac13$, so this is not a plain pigeonhole statement; it is the *rigidity* part of the optimality of the $4\times4$ grid for sixteen points (Wengerodt): near the grid, strict separation forces every point to the grid position by a second-order argument, and away from the grid a finite subdivision argument applies.
--
--   **Formalization Note.** Points are elements of `ℝ × ℝ`; `sqDist` is the squared Euclidean distance; the hypothesis is stated for all ordered pairs of distinct cell indices; the cells are closed.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (the optimality of the 4x4 grid, d_16 = 1/3); the decomposition into an occupancy statement and a labelled statement is proposed here.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem sixteen_quarter_cells_struct (p : Fin 4 → Fin 4 → Point)
    (hc : ∀ i j, (i.val : ℝ) / 4 ≤ (p i j).1 ∧ (p i j).1 ≤ ((i.val : ℝ) + 1) / 4 ∧
      (j.val : ℝ) / 4 ≤ (p i j).2 ∧ (p i j).2 ≤ ((j.val : ℝ) + 1) / 4)
    (hd : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l)) : False := by sorry
