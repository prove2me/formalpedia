-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mem_F_map_partition_trivial_on
-- name    : CannonFloydParry.exists_mem_F_map_partition_trivial_on
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:27:41.569671+00:00
-- url     : https://prove2.me/theorems/0f2463ca-85b0-40f9-8be4-99bf5170239d
-- title:
--   Transitivity on dyadic partitions, trivially on a common interval
-- statement:
--   Let $0 = x_0 < \cdots < x_n = 1$ and $0 = y_0 < \cdots < y_n = 1$ be dyadic partitions of
--   $[0,1]$ as in the previous statement, and suppose that for some index $i$ with $1 \le i \le n$
--   one has $x_{i-1} = y_{i-1}$ and $x_i = y_i$. Then the element $f$ of $F$ carrying each $x_j$ to
--   $y_j$ may in addition be taken to fix every point of the interval $[x_{i-1}, x_i]$.
--
--   The map is permitted to depend on the index $i$; the claim is not that one map is trivial on
--   every interval where the partitions happen to agree.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Lemma 4.2, p. 229, second sentence

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_mem_F_map_partition_trivial_on {n : ℕ} (x y : Fin (n + 1) → UI)
    (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : (x 0 : ℝ) = 0) (hxn : (x (Fin.last n) : ℝ) = 1)
    (hy0 : (y 0 : ℝ) = 0) (hyn : (y (Fin.last n) : ℝ) = 1)
    (hxd : ∀ i, IsDyadic (x i : ℝ)) (hyd : ∀ i, IsDyadic (y i : ℝ))
    (i : Fin n) (hi1 : x i.castSucc = y i.castSucc) (hi2 : x i.succ = y i.succ) :
    ∃ f ∈ F, (∀ j, f (x j) = y j) ∧
      ∀ z : UI, (x i.castSucc : ℝ) ≤ (z : ℝ) → (z : ℝ) ≤ (x i.succ : ℝ) → f z = z := by
  sorry

end CannonFloydParry
