-- Prove2me | Theorems.Thm_Apery_class_sum_approx
-- name    : Apery.class_sum_approx
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:06:24.471773+00:00
-- url     : https://prove2.me/theorems/03ef8138-cdf4-415e-854b-9f7b27c46e87
-- title:
--   Class sums versus their continuous limit: error $\le \frac52\sum|b_{ij}|$
-- statement:
--   For odd $p = 2m+1$, $v, v' < p$ and any $h : \mathbb N^2 \to \mathbb R$, the per-class sum over the class counts $a_c$ differs from the continuous limit $p\sum_{i,j} b_{ij}\,c_{ij}(v/p, v'/p)$ by at most $\frac52\sum_{i,j}|b_{ij}|$, where $b_{ij}$ are the coefficients in the basis $1, A, E$ and $c_{ij}$ the continuous interval counts. This is `class_sum_approx` of `Apery/Growth/ClassSum.lean` (the quantitive class-sum expansion at the heart of the inner/outer per-prime bounds). **Formalization Note** `aCnt`, `bcoef`, `ccount` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/ClassSum.lean#L108-L165

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem class_sum_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) -
      (p : ℝ) * ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 * ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| := by
  sorry

end Apery
