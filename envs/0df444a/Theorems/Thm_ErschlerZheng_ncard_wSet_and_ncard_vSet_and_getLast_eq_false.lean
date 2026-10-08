-- Prove2me | Theorems.Thm_ErschlerZheng_ncard_wSet_and_ncard_vSet_and_getLast_eq_false
-- name    : ErschlerZheng.ncard_wSet_and_ncard_vSet_and_getLast_eq_false
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T04:09:04.878353+00:00
-- url     : https://prove2.me/theorems/de450eb0-66f6-458e-ab80-28f65c8548db
-- title:
--   p. 37 — |W^n_k| = 2^{k/D} for D | n, k; |V^j_k| = 2^{k/D}; and every v ∈ V^j_k ends with the digit 0
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`). Then:
--
--   1. for all $n$ and $k$ divisible by $D$, the set $\mathsf W^n_k$ of (7.2) (`wSet`) has $2^{k/D}$ elements;
--   2. for every $j$ and every $k$ divisible by $D$, the set $\mathsf V^j_k$ of (7.3) (`vSet`) has $2^{k/D}$ elements, and every $v \in \mathsf V^j_k$ ends with the digit $0$.
--
--   Erschler and Zheng, p. 37: “For $k, n \in \mathbb N$ both divisible by $D$, define the set $\mathsf W^n_k$ of vertices of depth $k$ such that $u_i = 1$ except for those $i$ with $n + i \in I_\omega$, (7.2) $\mathsf W^n_k := \{u \in \mathsf L_k : u = u_1 \ldots u_k,\ u_i = 1 \text{ if } n + i \notin I_\omega\}$. Recall that the set $I_\omega$ is defined in Notation 7.1. The cardinality of the set $\mathsf W^n_k$ is $2^{k/D}$.” and “It is important that any $v \in \mathsf V^j_k$ ends with digit $0$. The cardinality of the set $V^j_k$ is $2^{k/D}$, the same as the cardinality of $\mathsf W^{j+D-\bar j}_k$.”
--
--   The cardinality of $\mathsf V^j_k$ is stated for $k$ divisible by $D$, as in the definition of $\mathsf V^j_k$ (“Let $k$ be an integer divisible by $D$”); $j$ is any integer, and $j + D - \bar j$ is then divisible by $D$ as (7.2) requires. The last sentence prints $V^j_k$ for $\mathsf V^j_k$. The sets are counted as sets of finite words (`Set.ncard`). The standing assumption is that of §7.2 (p. 35).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 37, the index sets (7.2)–(7.3)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem ncard_wSet_and_ncard_vSet_and_getLast_eq_false (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) :
    (∀ n k, D ∣ n → D ∣ k → (wSet D ω n k).ncard = 2 ^ (k / D)) ∧
    ∀ j k, D ∣ k →
      (vSet D ω j k).ncard = 2 ^ (k / D) ∧ ∀ v ∈ vSet D ω j k, v.getLast? = some false := by
  sorry

end ErschlerZheng
