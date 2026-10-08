-- Prove2me | Theorems.Thm_ErschlerZheng_setOf_not_mem_letterGerms_seqG_eq
-- name    : ErschlerZheng.setOf_not_mem_letterGerms_seqG_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T08:00:57.170501+00:00
-- url     : https://prove2.me/theorems/bd27a94c-e65c-49d5-afaa-d5b55dbaa8c3
-- title:
--   p. 55 — for ω_{j−1} = 2, the points where g_j has germ outside ℋ^b are the x_1…x_{j+1}1^∞ with j + 1 + Σx_i odd
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`) and let $j \ge 1$ with $\omega_{j-1} = \mathbf 2$. Then the set of points $x$ of the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) at which the germ of $g_j$ (`seqG`) is not in the groupoid $\mathcal H^b$ of $\langle b \rangle$-germs (`letterGerms ω .b`) is the set of rays $x_1 \ldots x_{j+1}1^\infty$ (`prepend`) with $j + 1 + \sum_{i=1}^{j+1} x_i$ odd.
--
--   Erschler and Zheng, p. 55: “We now return to the proof of Proposition 7.12. For $1 \leqslant j \leqslant n - k_n$ and $\omega_{j-1} = \mathbf 2$, $\gamma_j = g_j$, we have $B_j = \{x : (g_j, x) \notin \mathcal H\} = \{x : x_1 \ldots x_{j+1}1^\infty,\ j + 1 + \sum_{i=1}^{j+1} x_i \text{ is odd}\}$.”
--
--   The set $B_j$ involves $g_j$ only, so the statement has no $n$; the condition $j \le n - k_n$ of the sentence is what makes $\gamma_j = g_j$. $\mathcal H$ is $\mathcal H^b$, the groupoid of p. 42 (“Let $H = \langle b \rangle < (\mathcal G_\omega)_o$ and $\mathcal H^b$ be the set of germs that are either trivial or $b$ as in (3.1).”), and $x$ ranges over the orbit $o \cdot G$, $o = 1^\infty$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 55, the bad points of g_j

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem setOf_not_mem_letterGerms_seqG_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : ω (j - 1) = 2) :
    {x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} =
      {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
        x = prepend p oneRay} := by
  sorry

end ErschlerZheng
