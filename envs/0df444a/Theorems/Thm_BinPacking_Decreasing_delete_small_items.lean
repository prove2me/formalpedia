-- Prove2me | Theorems.Thm_BinPacking_Decreasing_delete_small_items
-- name    : BinPacking.Decreasing.delete_small_items
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:14:48.806063+00:00
-- url     : https://prove2.me/theorems/7337ec4c-a5b4-4eac-b996-7e194d3d1db6
-- title:
--   Lemma 3.3 — deleting elements at most $(r-1)/r$ preserves $FFD(L)>rL^*+d$ (and likewise for BFD)
-- statement:
--   Let $L$ be a list of real numbers in $(0,1]$, let $r\ge 1$ and $d\ge 1$ be real numbers, and let $L'$ be the list obtained from $L$ by deleting all elements not exceeding $(r-1)/r$, i.e. keeping exactly the elements $a$ with $a>(r-1)/r$ (in their original order).
--
--   1. If $FFD(L)>rL^*+d$, then $FFD(L')>rL'^*+d$.
--   2. If $BFD(L)>rL^*+d$, then $BFD(L')>rL'^*+d$.
--
--   In symbols, for $A\in\{FFD, BFD\}$,
--   $$A(L)>r\,L^*+d\ \Longrightarrow\ A(L')>r\,L'^*+d .$$
--
--   With $r=11/9$ one has $(r-1)/r=2/11$, so a counterexample to Theorem 3.2 would survive the deletion of all elements at most $2/11$; the lemma reduces Theorem 3.2 to lists contained in $(2/11,1]$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 309, Lemma 3.3

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Lemma 3.3 (p. 309): if `FFD(L) > r L* + d` with `r, d ≥ 1`, then the list `L'` obtained
from `L` by deleting all elements not exceeding `(r − 1)/r` also has `FFD(L') > r L'* + d`;
the same holds with BFD in place of FFD. -/
theorem delete_small_items (L : List ℝ) (hL : IsList L) (r d : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    ((FFD L : ℝ) > r * (optBins L : ℝ) + d →
      (FFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) >
        r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d) ∧
    ((BFD L : ℝ) > r * (optBins L : ℝ) + d →
      (BFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) >
        r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d) := by sorry

end BinPacking.Decreasing
