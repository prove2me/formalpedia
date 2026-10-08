-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_gTilde_mem_levelStab
-- name    : ErschlerZheng.not_forall_gTilde_mem_levelStab
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:58.856989+00:00
-- url     : https://prove2.me/theorems/112428a7-8b4d-4e1b-985b-3281547d2c3e
-- title:
--   Lemma 7.9, as printed, fails — g̃^v_j need not fix level j
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every $j \ge 1$, every positive $k$ divisible by $D$ and every $v \in \mathsf V^j_k$ (`vSet`), the element $\tilde g^v_j$ (`gTilde`) lies in the level stabilizer $\mathrm{St}_{G_\omega}(\mathsf L_j)$ (`levelStab`).
--
--   Erschler and Zheng, p. 39, Lemma 7.9: “The element $\tilde g^v_j$ is well defined (the substitutions $\zeta_{\omega_i}$'s can be applied). It is in the $j$-th level stabilizer and when $\omega_{j-1} \neq \mathbf 1$, the sections of $\tilde g^v_j$ at vertices of $\mathsf L_j$ are in $\{a\mathfrak c^v_j, \mathfrak c^v_j a\}$.”
--
--   The statement is the negation of the claim “It is in the $j$-th level stabilizer” as printed, which carries no condition on $\omega_{j-1}$. It fails for $\omega = (\mathbf{201})^\infty$, $D = 3$, $j = 3$, where $\omega_{j-1} = \mathbf 1$. Under the condition $\omega_{j-1} \neq \mathbf 1$ the claim holds; that is the milestone `ErschlerZheng.exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem`, and the sets $\mathfrak F_{j,n}$ of (7.7) use $\tilde g^v_j$ only when $\omega_{j-1} = \mathbf 2$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 39, Lemma 7.9 as printed (fails when ω_{j−1} = 1)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem not_forall_gTilde_mem_levelStab :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ j, 1 ≤ j → ∀ k, 0 < k → D ∣ k →
      ∀ v ∈ vSet D ω j k, gTilde ω j v ∈ levelStab (grigorchuk ω) j := by
  sorry

end ErschlerZheng
