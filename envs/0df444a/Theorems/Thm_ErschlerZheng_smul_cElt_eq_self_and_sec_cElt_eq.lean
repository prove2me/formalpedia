-- Prove2me | Theorems.Thm_ErschlerZheng_smul_cElt_eq_self_and_sec_cElt_eq
-- name    : ErschlerZheng.smul_cElt_eq_self_and_sec_cElt_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T04:34:09.184432+00:00
-- url     : https://prove2.me/theorems/e7667dd5-2b8d-4953-a310-071b76bcec22
-- title:
--   Lemma 7.7 — 𝔠^v_j fixes v; off the path v its only non-trivial sections are at v_1…v_i0 with ω_{j+i} ≠ 1, equal to bab or a, and its section at v is c_{𝔰^{j+k′}ω}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $D$ divide $k$, let $v \in \mathsf V^j_k$ (`vSet`), of length $k'$, and let $\mathfrak c = \mathfrak c^v_j$ (`cElt`). Then:
--
--   1. $v \cdot \mathfrak c = v$;
--   2. for every $0 \le i \le k'-1$, the section of $\mathfrak c$ (`sec`) at the vertex $v_1 \ldots v_i\bar v_{i+1}$ that leaves the path $v$ at depth $i+1$ ($\bar v_{i+1}$ is the other digit) is trivial, unless $v_{i+1} = 1$ and $\omega_{j+i} \ne \mathbf 1$;
--   3. for every $0 \le i \le k'-2$ with $\omega_{j+i} \ne \mathbf 1$: $v_{i+1} = 1$, and the section of $\mathfrak c$ at $v_1 \ldots v_i0$ is $b_{\mathfrak s^{j+i+1}\omega}\,a\,b_{\mathfrak s^{j+i+1}\omega}$ if $v_{i+2} = 0$ and $a$ otherwise;
--   4. the section of $\mathfrak c$ at $v$ is $c_{\mathfrak s^{j+k'}\omega}$.
--
--   Erschler and Zheng, p. 38, Lemma 7.7: “Let $v \in \mathsf V^j_k$, $D|k$ and write $k' = |v|$ the length of $v$. The vertex $v$ is fixed by $\mathfrak c^v_j$ and along the ray segment $v$ the only nontrivial sections of $\mathfrak c^v_j$ are at $\{v_1 \ldots v_i0 : \omega_{j+i} \neq \mathbf 1,\ 0 \leqslant i \leqslant k'-1\}$. Among these, for $i \leqslant k'-2$ and $\omega_{j+i} \neq \mathbf 1$, if $v_{i+2} = 0$ then the section at $v_1 \ldots v_i0$ is $b_{\mathfrak s^{j+i+1}\omega}ab_{\mathfrak s^{j+i+1}\omega}$, otherwise the section is $a$. For $i = k'-1$, at level $k'$, the only non-trivial section is $c_{\mathfrak s^{j+k'}\omega}$ at $v$.”
--
--   “Along the ray segment $v$” is read as the sections at the vertices adjacent to the path $v$, one at each depth $1, \ldots, k'$, and at $v$ itself. Clause 2 says the listed set contains every such vertex with a non-trivial section: $v_1 \ldots v_i0$ leaves the path exactly when $v_{i+1} = 1$. Clause 3 makes explicit that for $\omega_{j+i} \neq \mathbf 1$ the vertex $v_1 \ldots v_i0$ is indeed off the path; at $i = k'-1$ the last digit of $v$ is $0$ ([`ErschlerZheng.ncard_wSet_and_ncard_vSet_and_getLast_eq_false`](https://prove2.me/theorems/de450eb0-66f6-458e-ab80-28f65c8548db)) and $\omega_{j+k'-1} = \mathbf 1$ ([`ErschlerZheng.length_and_hElt_mem_rist_and_oneRay_smul_hProd`](https://prove2.me/theorems/d9949906-c0e1-49c1-b297-a6bb20d4b23e)), so clause 2 makes the section at the sibling of $v$ trivial, and clause 4 is the remaining sentence. The assumption $(\mathrm{Fr}(D))$ is the standing assumption of §7.2 (p. 35).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 38, Lemma 7.7

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem smul_cElt_eq_self_and_sec_cElt_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (j k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) :
    v <• cElt ω j v = v ∧
    (∀ i (hi : i < v.length), (v[i] = true → ω (j + i) = 1) →
      sec (cElt ω j v) (v.take i ++ [!v[i]]) = 1) ∧
    (∀ i (hi : i + 2 ≤ v.length), ω (j + i) ≠ 1 →
      v[i] = true ∧
        sec (cElt ω j v) (v.take i ++ [false]) =
          if v[i + 1] = false then
            gen (shiftSeq ω (j + i + 1)) .b * Garrido.grigA * gen (shiftSeq ω (j + i + 1)) .b
          else Garrido.grigA) ∧
    sec (cElt ω j v) v = gen (shiftSeq ω (j + v.length)) .c := by
  sorry

end ErschlerZheng
