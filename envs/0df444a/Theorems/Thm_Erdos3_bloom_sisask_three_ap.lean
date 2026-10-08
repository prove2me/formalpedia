-- Prove2me | Theorems.Thm_Erdos3_bloom_sisask_three_ap
-- name    : Erdos3.bloom_sisask_three_ap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:24:33.359375+00:00
-- url     : https://prove2.me/theorems/2b80ee26-28b0-4f3a-9749-1f55cb0d15d4
-- title:
--   Case $k=3$ of the goal (Bloom–Sisask)
-- statement:
--   If $A\subseteq\mathbb N$ satisfies $\sum_{n\in A}1/n=\infty$, then $A$ contains a three-term arithmetic progression $a,a+d,a+2d$ with $d>0$. This is the case $k=3$ of the goal, first established by Bloom and Sisask (2020) as a consequence of their bound on $r_3(N)$.
-- source:
--   T. F. Bloom and O. Sisask, *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*, arXiv:2007.03528 (2020), Corollary 1.2; cited at https://www.erdosproblems.com/3

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem bloom_sisask_three_ap : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) → ∃ S ⊆ A, IsAPOfLength S 3 := by
  sorry

end Erdos3
