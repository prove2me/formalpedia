-- Prove2me | Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
-- name    : ErschlerZheng.exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T04:59:02.325857+00:00
-- url     : https://prove2.me/theorems/d686b935-0269-4956-802d-2b5206cf304b
-- title:
--   Lemma 7.9, corrected — a𝔠^v_j is the value of a word in ab, ac, ad, so g̃^v_j ∈ G_ω is defined; when ω_{j−1} ≠ 1, g̃^v_j fixes level j and its sections there are a𝔠^v_j or 𝔠^v_j a
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $j \ge 1$, let $D$ divide $k$ and let $v \in \mathsf V^j_k$ (`vSet`). Then:
--
--   1. $a\mathfrak c^v_j$ (`cElt`) is the value in $G_{\mathfrak s^j\omega}$ of some word in the free group on the pairs $ab, ac, ad$ (`evalFree ω j`);
--   2. $\tilde g^v_j$ (`gTilde`) lies in $G_\omega$ (`grigorchuk ω`);
--   3. if $\omega_{j-1} \neq \mathbf 1$, then $\tilde g^v_j$ lies in the level stabilizer $\mathrm{St}_{G_\omega}(\mathsf L_j)$ (`levelStab`), and its section (`sec`) at every vertex of level $j$ is $a\mathfrak c^v_j$ or $\mathfrak c^v_j a$.
--
--   Erschler and Zheng, p. 39, Lemma 7.9: “The element $\tilde g^v_j$ is well defined (the substitutions $\zeta_{\omega_i}$'s can be applied). It is in the $j$-th level stabilizer and when $\omega_{j-1} \neq \mathbf 1$, the sections of $\tilde g^v_j$ at vertices of $\mathsf L_j$ are in $\{a\mathfrak c^v_j, \mathfrak c^v_j a\}$.”
--
--   *Correction.* As printed, the second sentence puts $\tilde g^v_j$ in the $j$-th level stabilizer for every $\omega_{j-1}$. That fails when $\omega_{j-1} = \mathbf 1$ ([`ErschlerZheng.not_forall_gTilde_mem_levelStab`](https://prove2.me/theorems/112428a7-8b4d-4e1b-985b-3281547d2c3e)). The statement asserts the stabilizer claim under the condition $\omega_{j-1} \neq \mathbf 1$ that the printed sentence attaches to the sections. The sets $\mathfrak F_{j,n}$ of (7.7) use $\tilde g^v_j$ only when $\omega_{j-1} = \mathbf 2$.
--
--   “The substitutions $\zeta_{\omega_i}$'s can be applied” is clause 1: by p. 15, a substitution can be applied to an element represented by a word in $ab, ac, ad$, and each substitution maps such words to such words, so once $a\mathfrak c^v_j$ has a representing word every stage of $\zeta_{\omega_0} \circ \cdots \circ \zeta_{\omega_{j-1}}$ is applied to the value of a word. That the result does not depend on the word chosen is the milestone [`ErschlerZheng.evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne`](https://prove2.me/theorems/51e4b918-c217-4cda-bcf8-be15424445b3), whose condition on the tail of $\omega$ Assumption $(\mathrm{Fr}(D))$ supplies at every level ([`ErschlerZheng.exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr`](https://prove2.me/theorems/10b40a56-7193-4cf0-8ff5-5ebe2179a42c)). Clause 2 records that the result is in $G_\omega$, as (7.6) intends (“to obtain an element in $G_\omega$”, p. 39). The assumption $(\mathrm{Fr}(D))$ is the standing assumption of §7.2 (p. 35), and $j \ge 1$ makes $\omega_{j-1}$ a letter of $\omega$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 39, Lemma 7.9, corrected

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) (hk : D ∣ k) (v : List Bool)
    (hv : v ∈ vSet D ω j k) :
    (∃ w : FreeGroup APair, evalFree ω j w = Garrido.grigA * cElt ω j v) ∧
    gTilde ω j v ∈ grigorchuk ω ∧
    (ω (j - 1) ≠ 1 → gTilde ω j v ∈ levelStab (grigorchuk ω) j ∧
      ∀ u : List Bool, u.length = j →
        sec (gTilde ω j v) u = Garrido.grigA * cElt ω j v ∨
          sec (gTilde ω j v) u = cElt ω j v * Garrido.grigA) := by
  sorry

end ErschlerZheng
