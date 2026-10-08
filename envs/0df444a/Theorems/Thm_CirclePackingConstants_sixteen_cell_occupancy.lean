-- Prove2me | Theorems.Thm_CirclePackingConstants_sixteen_cell_occupancy
-- name    : CirclePackingConstants.sixteen_cell_occupancy
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T12:16:01.780176+00:00
-- url     : https://prove2.me/theorems/e57bcd48-b8a0-44ee-b87e-7ef98d1f0c6c
-- title:
--   Sixteen points of the unit square with pairwise $|p-q|^2>\tfrac19$ occupy the sixteen cells of the $4\times4$ subdivision bijectively
-- statement:
--   Let $p_0,\dots,p_{15}$ be sixteen points of the closed unit square whose pairwise squared distances all exceed $\tfrac19$. Let $Q_{ij}=[\tfrac i4,\tfrac{i+1}4]\times[\tfrac j4,\tfrac{j+1}4]$ ($i,j\in\{0,1,2,3\}$) be the sixteen closed cells of the $4\times4$ subdivision. Then the points can be labelled by the cells, i.e. there is a bijection $\sigma:\{0,\dots,15\}\to\{0,1,2,3\}^2$ with $p_k\in Q_{\sigma(k)}$ for every $k$: every cell contains exactly one of the points.
--
--   A cell has diameter $\sqrt2/4\approx0.354>\tfrac13$, so two points may a priori share a cell (near opposite corners, in squares of side about $0.03$); the statement says that this cannot happen when all sixteen points are strictly more than $\tfrac13$ apart. Since the $4\times4$ grid of spacing $\tfrac13$ shows that the separation $\tfrac13$ is attained, this is the *global* (non-tight) half of the optimality proof for sixteen points: the numerically best configuration with a doubly occupied cell has minimum distance about $0.324<\tfrac13$, so there is a margin and a finite case analysis over the occupancy patterns of the cells applies.
--
--   **Formalization Note.** `Fin 4 × Fin 4` indexes the cells; the cells are closed, so a point on a common boundary may be assigned to either cell.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (the optimality of the 4x4 grid, d_16 = 1/3); the decomposition into an occupancy statement and a labelled statement is proposed here.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem sixteen_cell_occupancy (p : Fin 16 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hd : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) :
    ∃ σ : Fin 16 → Fin 4 × Fin 4, Function.Bijective σ ∧ ∀ k,
      ((σ k).1.val : ℝ) / 4 ≤ (p k).1 ∧ (p k).1 ≤ (((σ k).1.val : ℝ) + 1) / 4 ∧
      ((σ k).2.val : ℝ) / 4 ≤ (p k).2 ∧ (p k).2 ≤ (((σ k).2.val : ℝ) + 1) / 4 := by sorry
