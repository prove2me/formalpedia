-- Prove2me | Theorems.Thm_ErschlerZheng_exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr
-- name    : ErschlerZheng.exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:43.784368+00:00
-- url     : https://prove2.me/theorems/10b40a56-7193-4cf0-8ff5-5ebe2179a42c
-- title:
--   Supporting fact for Assumption Fr(D), not in the paper — the letters 1 and 2 occur in every tail of ω, so ω is neither eventually constant nor constant
-- statement:
--   Let $\omega = \omega_0\omega_1\ldots$ (`ω : ℕ → Fin 3`) satisfy Assumption $(\mathrm{Fr}(D))$ of Notation 7.1 (`SatisfiesFr D ω`). Then:
--
--   1. for every $n$ some $k > n$ has $\omega_k = \mathbf 1$, and some $k > n$ has $\omega_k = \mathbf 2$;
--   2. for every $n$ and every letter $i \neq \omega_n$, some $k > n$ has $\omega_k \neq i$;
--   3. there is no letter $i$ with $\omega_k = i$ for all large $k$ (`∀ᶠ k in Filter.atTop`);
--   4. some $m, n$ have $\omega_m \neq \omega_n$.
--
--   Clause 2 is, at each $n$, word for word the hypothesis on the tail in `ErschlerZheng.evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne`. Clause 3 is the hypothesis of `ErschlerZheng.forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const`, and clause 4 that of `ErschlerZheng.ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff`.
--
--   This is not a result of the paper. It backs sentences of four notes: the note of `evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne` (“which every string satisfying Assumption $(\mathrm{Fr}(D))$ meets”, and, in its *Correction*, “in which the letters $\mathbf 1$ and $\mathbf 2$ occur in every tail, so the assumption holds there for every $n$”); the note of `exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem`, which applies that milestone under Assumption $(\mathrm{Fr}(D))$; the note of `forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const` (“it holds under Assumption $(\mathrm{Fr}(D))$, the standing assumption of §7”); and the Construction bundle note `ErschlerZheng_Construction` (“when $\omega$ is not constant, as under Assumption $(\mathrm{Fr}(D))$”).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 34, Assumption Fr(D): the letters 1 and 2 occur in every tail (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr
    (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) :
    (∀ n, (∃ k, n < k ∧ ω k = 1) ∧ (∃ k, n < k ∧ ω k = 2)) ∧
    (∀ n, ∀ i : Fin 3, i ≠ ω n → ∃ k, n < k ∧ ω k ≠ i) ∧
    (¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i) ∧
    ∃ m n, ω m ≠ ω n := by
  sorry

end ErschlerZheng
