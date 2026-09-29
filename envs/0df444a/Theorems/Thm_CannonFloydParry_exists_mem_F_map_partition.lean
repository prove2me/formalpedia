-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mem_F_map_partition
-- name    : CannonFloydParry.exists_mem_F_map_partition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:27:06.026276+00:00
-- url     : https://prove2.me/theorems/ba1613ad-9215-4e49-bdfb-7213c39151da
-- title:
--   Transitivity of $F$ on dyadic partitions
-- statement:
--   Let $0 = x_0 < x_1 < \cdots < x_n = 1$ and $0 = y_0 < y_1 < \cdots < y_n = 1$ be two
--   partitions of $[0,1]$, with the same number of points, all of whose points are dyadic rational
--   numbers. Then there exists an element $f$ of Thompson's group $F$ with $f(x_i) = y_i$ for every
--   $i = 0, \dots, n$.
--
--   No relation between the two partitions is assumed beyond their having equally many points.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Lemma 4.2, p. 229, first sentence

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_mem_F_map_partition {n : ℕ} (x y : Fin (n + 1) → UI)
    (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : (x 0 : ℝ) = 0) (hxn : (x (Fin.last n) : ℝ) = 1)
    (hy0 : (y 0 : ℝ) = 0) (hyn : (y (Fin.last n) : ℝ) = 1)
    (hxd : ∀ i, IsDyadic (x i : ℝ)) (hyd : ∀ i, IsDyadic (y i : ℝ)) :
    ∃ f ∈ F, ∀ i, f (x i) = y i := by
  sorry

end CannonFloydParry
