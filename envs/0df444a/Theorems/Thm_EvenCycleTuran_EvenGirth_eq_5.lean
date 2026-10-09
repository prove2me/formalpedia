-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_eq_5
-- name    : EvenCycleTuran.EvenGirth.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:24.652044+00:00
-- url     : https://prove2.me/theorems/1af1c666-2ed6-495a-b1f2-c64b05ac9343
-- title:
--   (5), p. 23 — ½ Σ_{a≠b} C(f_l(a, b), 2) = O(n²) in a graph with no cycle of length 3, …, 2l−1 or 2k
-- statement:
--   Let $k>l\ge2$. There is a constant $C$, depending only on $k$ and $l$, such that for every $n$ and every graph $G$ on $n$ vertices containing no cycle of length $3,4,\dots,2l-1$ and no cycle of length $2k$,
--
--   $$\frac12\sum_{a\ne b,\ a,b\in V(G)}\binom{f_l(a,b)}{2}\le C\,n^2,$$
--
--   where $f_l(a,b)$ is the number of paths of $l$ edges between $a$ and $b$ and the sum runs over ordered pairs of distinct vertices.
--
--   This is display (5) of the paper; it feeds the case $m\ge3$ of Theorem 14.
--
--   **Formalization Note.** $O(n^2)$ is encoded with a constant chosen before $n$ and $G$. The page justifies (5) "by the case $m = 2$, since the left-hand side is equal to the number of $C_{2l}$'s in $G$"; in fact each $C_{2l}$ is counted once for each of its $l$ opposite pairs, which changes only the constant.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 23, display (5)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem eq_5 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1) ∪ {2 * k}) G →
        (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b ∈ univ.erase a, ((pathCount G l a b).choose 2 : ℝ)) ≤
          C * (n : ℝ) ^ 2 := by sorry

end EvenCycleTuran.EvenGirth
