-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_cell_occupancy
-- name    : CirclePackingConstants.twentyfive_cell_occupancy
-- status  : Open
-- author  : @vebis
-- created : 2026-10-07T06:17:57.755017+00:00
-- url     : https://prove2.me/theorems/a2118eae-3d22-4481-99ec-ef039a967c49
-- title:
--   Twenty-five points of the unit square with pairwise $|p-q|^2>\tfrac1{16}$ occupy the cells of the $5\times5$ subdivision bijectively
-- statement:
--   Let $p_0,\dots,p_{24}$ be twenty-five points of the closed unit square whose pairwise squared distances all exceed $\tfrac1{16}$, and let $Q_{ij}=[\tfrac i5,\tfrac{i+1}5]\times[\tfrac j5,\tfrac{j+1}5]$ be the cells of the $5\times5$ subdivision. Then there is a bijection $\sigma:\{0,\dots,24\}\to\{0,\dots,4\}^2$ with $p_k\in Q_{\sigma(k)}$ for every $k$: every cell contains exactly one of the points.
--
--   A cell has diameter $\sqrt2/5\approx0.283>\tfrac14$, so two points may a priori share a cell (near opposite corners); the statement says that this cannot happen when all points are strictly more than $\tfrac14$ apart. Since the $5\times5$ grid of spacing $\tfrac14$ shows that the separation $\tfrac14$ is attained, this is the global (non-tight) half of the optimality proof for twenty-five points: the numerically best configuration with a doubly occupied cell has minimum distance clearly below $\tfrac14$, so there is a margin and a finite case analysis over the occupancy patterns of the cells applies.
--
--   **Formalization Note.** `Fin 5 × Fin 5` indexes the cells; the cells are closed, so a point on a common boundary may be assigned to either cell.
-- source:
--   G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie (1987) (optimality of the 5x5 grid, d_25 = 1/4); the decomposition into an occupancy statement and a labelled statement is proposed here.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem twentyfive_cell_occupancy (p : Fin 25 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hd : ∀ i j, i ≠ j → (1 : ℝ) / 16 < sqDist (p i) (p j)) :
    ∃ σ : Fin 25 → Fin 5 × Fin 5, Function.Bijective σ ∧ ∀ k,
      ((σ k).1.val : ℝ) / 5 ≤ (p k).1 ∧ (p k).1 ≤ (((σ k).1.val : ℝ) + 1) / 5 ∧
      ((σ k).2.val : ℝ) / 5 ≤ (p k).2 ∧ (p k).2 ≤ (((σ k).2.val : ℝ) + 1) / 5 := by sorry
