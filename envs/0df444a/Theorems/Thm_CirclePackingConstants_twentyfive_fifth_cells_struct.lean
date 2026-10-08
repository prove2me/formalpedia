-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_fifth_cells_struct
-- name    : CirclePackingConstants.twentyfive_fifth_cells_struct
-- status  : Open
-- author  : @vebis
-- created : 2026-10-07T06:18:02.139986+00:00
-- url     : https://prove2.me/theorems/2c92ff8b-6d8a-4581-9e7f-7a462e4de2d9
-- title:
--   Twenty-five points, one in each cell of the $5\times5$ subdivision, have a close pair
-- statement:
--   For $i,j\in\{0,1,2,3,4\}$ let $Q_{ij}=[\tfrac i5,\tfrac{i+1}5]\times[\tfrac j5,\tfrac{j+1}5]$ be the twenty-five closed cells of the $5\times5$ subdivision of the unit square, and let $p_{ij}\in Q_{ij}$ be one point in each cell. Then two of the twenty-five points are at distance at most $\tfrac14$:
--
--   $$\min_{(i,j)\neq(k,l)}|p_{ij}-p_{kl}|^2\le \tfrac1{16}.$$
--
--   Equivalently, it is impossible that all pairs satisfy $|p_{ij}-p_{kl}|^2>\tfrac1{16}$. The bound is sharp: the grid $p_{ij}=(\tfrac i4,\tfrac j4)$ lies in the cells and has minimal squared distance exactly $\tfrac1{16}$. A cell has diameter $\sqrt2/5>\tfrac14$, so this is not a plain pigeonhole statement; it is the rigidity part of the optimality of the $5\times5$ grid for twenty-five points (Wengerodt).
--
--   **Formalization Note.** Points are elements of `ℝ × ℝ`; `sqDist` is the squared Euclidean distance; the hypothesis is stated for all ordered pairs of distinct cell indices; the cells are closed.
-- source:
--   G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie (1987) (optimality of the 5x5 grid, d_25 = 1/4); the decomposition into an occupancy statement and a labelled statement is proposed here.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem twentyfive_fifth_cells_struct (p : Fin 5 → Fin 5 → Point)
    (hc : ∀ i j, (i.val : ℝ) / 5 ≤ (p i j).1 ∧ (p i j).1 ≤ ((i.val : ℝ) + 1) / 5 ∧
      (j.val : ℝ) / 5 ≤ (p i j).2 ∧ (p i j).2 ≤ ((j.val : ℝ) + 1) / 5)
    (hd : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 16 < sqDist (p i j) (p k l)) : False := by sorry
