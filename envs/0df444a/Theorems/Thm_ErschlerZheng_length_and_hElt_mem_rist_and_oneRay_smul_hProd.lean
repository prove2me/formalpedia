-- Prove2me | Theorems.Thm_ErschlerZheng_length_and_hElt_mem_rist_and_oneRay_smul_hProd
-- name    : ErschlerZheng.length_and_hElt_mem_rist_and_oneRay_smul_hProd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T04:19:44.179208+00:00
-- url     : https://prove2.me/theorems/d9949906-c0e1-49c1-b297-a6bb20d4b23e
-- title:
--   p. 38 — for v ∈ V^j_k, |v| = k′; each h^v_i with v_i = 0 lies in Rist(v_1…v_{i−2}) and [b, a] acts as b·a below 1; and 1^∞ · h^v_1⋯h^v_{k′} = v1^∞
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $D$ divide $k$, and let $v \in \mathsf V^j_k$ (`vSet`). Then:
--
--   1. $v$ has length $k' = D - \bar j + k + m_{\ell(k,j)} + 3$, where $\bar j$ is the residue of $j$ mod $D$ and $m_\ell$ is `frM D ω ℓ`;
--   2. for every $i \ge 1$ with $v_i = 0$: the string $\omega_{j+i-3}\omega_{j+i-2}\omega_{j+i-1}$ is $\mathbf{201}$ or $\mathbf{211}$; the element $h^v_i$ (`hElt`) lies in the rigid stabilizer of the vertex $v_1 \ldots v_{i-2}$ in $G_{\mathfrak s^j\omega}$ (`rist`); and the commutator $[b_{\mathfrak s^{j+i-2}\omega}, a]$ fixes the vertex $1$, where its section (`sec`) is $b_{\mathfrak s^{j+i-1}\omega}a$;
--   3. $1^\infty \cdot h^v_1 h^v_2 \cdots h^v_{k'} = v1^\infty$ (`hProd`, `prepend`).
--
--   Erschler and Zheng, p. 38: “Given a vertex $v = v_1 \ldots v_{k'} \in \mathsf V^j_k$, where $k' = D - \bar j + k + m_{\ell(j,k)} + 3$ denotes the length of $v$, take the following sequence of elements in $G_j = G_{\mathfrak s^j\omega}$:” and, after (7.4), “By definition of $\mathsf V^j_k$ in (7.3), if $v_i = 0$ then the string $\omega_{j+i-3}\omega_{j+i-2}\omega_{j+i-1}$ is either $\mathbf{201}$ or $\mathbf{211}$. Since the digit $\omega_{j+i-3}$ in this case must be $\mathbf 2$, by Fact 7.6, $[b_{\mathfrak s^{j+i-2}\omega}, a]$ is in the rigid stabilizer of the vertex $v_1 \ldots v_{i-2}$ in $G_j$. The letter following $\omega_{j+i-3}$ is different from $\mathbf 2$, therefore $[b_{\mathfrak s^{j+i-2}\omega}, a]$ acts as $b_{\mathfrak s^{j+i-1}\omega}a$ on the right subtree. Since $h^v_i$ is in the rigid stabilizer of $v_1 \ldots v_{i-2}$, it is easy to verify recursively that by definition of the elements $h^v_i$ in (7.4), we have $1^\infty \cdot h^v_1 h^v_2 \ldots h^v_{k'} = v1^\infty$.”
--
--   The rigid-stabilizer claim is stated for $h^v_i = \iota([b_{\mathfrak s^{j+i-2}\omega}, a], v_1 \ldots v_{i-2})$, the element that the last sentence of the quotation says is in that stabilizer. “Acts as $b_{\mathfrak s^{j+i-1}\omega}a$ on the right subtree” is stated as: the commutator fixes the vertex $1$ and its section there is $b_{\mathfrak s^{j+i-1}\omega}a$. The paper writes $\ell(k, j)$ in (7.3)'s definition and $m_{\ell(j,k)}$ here; both are the same index.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 38, the elements (7.4)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions commutatorElement

namespace ErschlerZheng

theorem length_and_hElt_mem_rist_and_oneRay_smul_hProd (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 ∧
    (∀ i, 1 ≤ i → v[i - 1]? = some false →
      (ω (j + i - 3) = 2 ∧ (ω (j + i - 2) = 0 ∨ ω (j + i - 2) = 1) ∧ ω (j + i - 1) = 1) ∧
      hElt ω j v i ∈ rist (grigorchuk (shiftSeq ω j)) (v.take (i - 2)) ∧
      [true] <• ⁅gen (shiftSeq ω (j + i - 2)) .b, Garrido.grigA⁆ = [true] ∧
      sec ⁅gen (shiftSeq ω (j + i - 2)) .b, Garrido.grigA⁆ [true] =
        gen (shiftSeq ω (j + i - 1)) .b * Garrido.grigA) ∧
    oneRay <• hProd ω j v = prepend v oneRay := by
  sorry

end ErschlerZheng
