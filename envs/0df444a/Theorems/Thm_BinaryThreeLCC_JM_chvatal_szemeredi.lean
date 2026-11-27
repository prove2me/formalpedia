-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_chvatal_szemeredi
-- name    : BinaryThreeLCC.JM.chvatal_szemeredi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:39.874222+00:00
-- url     : https://prove2.me/theorems/0adc6947-fa82-4266-a92c-57231509d475
-- title:
--   Chvátal–Szemerédi: short directed cycles under minimum out-degree
-- statement:
--   Let $R$ be a binary relation (a directed graph, loops allowed) on a finite type $V$, let $S\subseteq V$ be nonempty, and let $r\ge1$ be an integer. Suppose every $x\in S$ has at least $r$ out-neighbours inside $S$, i.e. $|\{y\in S: xRy\}|\ge r$. Then there are $\ell\ge1$ and pairwise distinct vertices $w_0,\dots,w_{\ell-1}\in S$ with
--
--   $$w_0\,R\,w_1\,R\,\cdots\,R\,w_{\ell-1}\,R\,w_0\qquad\text{and}\qquad \ell\,(r+1)\le 2|S| .$$
--
--   That is, a digraph on $|S|$ vertices with minimum out-degree $r$ contains a directed cycle of length at most $2|S|/(r+1)$. A loop is a cycle of length one.
--
--   In the decomposition of the Janzer–Manohar lower bound this replaces the Eulerian short-cycle theorem (Fact 3.4): it yields arc-disjoint short cycles covering a constant fraction of the arcs of a digraph with linear minimum out-degree.
--
--   **Formalization Note** The cycle is an injective map $w:\mathrm{Fin}\,\ell\to V$ and the successor of index $i$ is `finRotate l i`.
-- source:
--   V. Chvátal and E. Szemerédi, Short cycles in directed graphs, J. Combin. Theory Ser. B 35 (1983) 323–327, Theorem; exposition in B. D. Sullivan, arXiv:math/0603469, Theorem 1. Used in place of Fact 3.4 of Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem chvatal_szemeredi {V : Type} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (S : Finset V) (r : ℕ) (hr : 0 < r)
    (hS : S.Nonempty) (hdeg : ∀ x ∈ S, r ≤ (S.filter (fun y => R x y)).card) :
    ∃ (l : ℕ) (w : Fin l → V), 0 < l ∧ ((l : ℝ) * (r + 1) ≤ 2 * S.card) ∧
      Function.Injective w ∧ (∀ i, w i ∈ S) ∧ ∀ i : Fin l, R (w i) (w (finRotate l i)) := by sorry

end BinaryThreeLCC.JM
