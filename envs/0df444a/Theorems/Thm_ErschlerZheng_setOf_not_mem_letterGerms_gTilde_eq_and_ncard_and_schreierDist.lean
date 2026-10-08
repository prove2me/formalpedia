-- Prove2me | Theorems.Thm_ErschlerZheng_setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist
-- name    : ErschlerZheng.setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T07:45:56.595855+00:00
-- url     : https://prove2.me/theorems/15780cf7-f74b-4bea-a4db-7f5b9d88dd75
-- title:
--   (7.16) — the points where g̃^v_j has germ outside ℋ^b are the x_1…x_{j+1}v_2…v_{D−j̄+2k_n}1^{m+2}01^∞ with j + 1 + Σx_i odd; there are 2^j of them, at distance ≍ 2^{j+2k_n} from 1^∞
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`) and let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`). Then there are constants $c, C > 0$ such that for every $n$ divisible by $D$, every $1 \le j \le n$ with $\omega_{j-1} = \mathbf 2$ and $n - k_n < j$ (written $n < j + k_n$), and every $v \in \mathsf V^j_{2k_n}$ (`vSet`) with $|1^\infty \wedge v| \ge n - j + D$, the set $B(j, v)$ of points $x$ of the orbit $1^\infty \cdot G_\omega$ (`orbitOne`) at which the germ of $\tilde g^v_j$ (`gTilde`) is not in the groupoid $\mathcal H^b$ of $\langle b \rangle$-germs (`letterGerms ω .b`) satisfies:
--
--   1. $B(j, v)$ is the set of rays $x_1 \ldots x_{j+1}\, v_2 \ldots v_{D-\bar j+2k_n}\, 1^{m+2}0\, 1^\infty$ with $j + 1 + \sum_{i=1}^{j+1} x_i$ odd, where $m = m_{\ell(2k_n, j)}$ (`frM`, `ellIndex`) and $\bar j$ is the residue of $j$ mod $D$;
--   2. $B(j, v)$ has $2^j$ elements;
--   3. every $x \in B(j, v)$ has Schreier distance (`schreierDist`) from $1^\infty$ between $c\,2^{j+2k_n}$ and $C\,2^{j+2k_n}$.
--
--   Erschler and Zheng, p. 53: “For $n - k_n < j \leqslant n$ such that $\omega_{j-1} = \mathbf 2$, by definition of the set $\mathfrak F_{j,n}$ in (7.7), an element $\gamma_j \in \mathfrak F_{j,n}$ is of the form $\gamma_j = \tilde g^v_j = \zeta_{\omega_0} \circ \ldots \circ \zeta_{\omega_{j-1}}(a\mathfrak c^v_j)$, where $v = 1^{D-\bar j}u1^{m+1}0$, $u \in \mathsf W^{j+D-\bar j}_{2k_n}$, $m = m_{\ell(j,2k_n)} \in \{0, 1, \ldots, D-3\}$ and $|1^\infty \wedge v| \geqslant n - j + D$. It follows from Lemma 7.7 that the collection of points which carry germs not in $\mathcal H$ is exactly (7.16) $B(j, v) := \{x : (\tilde g^v_j, x) \notin \mathcal H\} = \{x : x = x_1 \ldots x_{j+1}v_2 \ldots v_{D-\bar j+2k_n}1^{m+2}01^\infty : j + 1 + \sum_{i=1}^{j+1} x_i \text{ is odd}\}$. In particular, the cardinality of this set is $2^j$ and on the Schreier graph the distance from a point in this set to $1^\infty$ is comparable to $2^{j+2k_n}$.”
--
--   $\mathcal H$ is $\mathcal H^b$, the groupoid of $\langle b \rangle$-germs of p. 42 (“Let $H = \langle b \rangle < (\mathcal G_\omega)_o$ and $\mathcal H^b$ be the set of germs that are either trivial or $b$ as in (3.1).”), and $x$ ranges over the orbit $o \cdot G$, $o = 1^\infty$. “Comparable to $2^{j+2k_n}$” is read as bounds above and below by constant multiples, with the constants independent of $n$, $j$ and $v$. The quotation writes $v = 1^{D-\bar j}u1^{m+1}0$ where (7.3) has $1^{m+2}0$; the set (7.16) uses $1^{m+2}0$, as does the statement, which follows (7.3).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 53, (7.16)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n, D ∣ n → ∀ j, 1 ≤ j → ω (j - 1) = 2 → n < j + k n →
      j ≤ n → ∀ v ∈ vSet D ω j (2 * k n), n - j + D ≤ commonPrefixLength v oneRay →
        {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b} =
            {x | ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧
              x = prepend (p ++ (v.drop 1).take (D - j % D + 2 * k n - 1) ++
                List.replicate (frM D ω (ellIndex D (2 * k n) j) + 2) true ++ [false]) oneRay} ∧
          {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b}.ncard = 2 ^ j ∧
          ∀ x ∈ {x | x ∈ orbitOne ω ∧ (gTilde ω j v, x) ∉ letterGerms ω .b},
            c * 2 ^ (j + 2 * k n) ≤ (schreierDist ω oneRay x : ℝ) ∧
              (schreierDist ω oneRay x : ℝ) ≤ C * 2 ^ (j + 2 * k n) := by
  sorry

end ErschlerZheng
