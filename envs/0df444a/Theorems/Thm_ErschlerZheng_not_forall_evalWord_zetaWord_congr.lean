-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_evalWord_zetaWord_congr
-- name    : ErschlerZheng.not_forall_evalWord_zetaWord_congr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:41.083517+00:00
-- url     : https://prove2.me/theorems/6eacbdd8-4d7b-4e14-b1db-e26bb207c258
-- title:
--   p. 15, as printed, fails — two words in ab, ac, ad with the same value can have ζ_{ω_n}-images with different values
-- statement:
--   It is not true that for every $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$, every $n$ and all words $w_1, w_2$ over the letters $ab, ac, ad$, if $w_1$ and $w_2$ have the same value in $G_{\mathfrak s^{n+1}\omega}$ then $\zeta_{\omega_n}(w_1)$ and $\zeta_{\omega_n}(w_2)$ have the same value in $G_{\mathfrak s^n\omega}$ (`evalWord`, `zetaWord`).
--
--   Erschler and Zheng, p. 15: “It follows from (2.3) that if $g \in G_{\mathfrak s^{n+1}\omega}$ can be represented by a word in $\{ab_{\mathfrak s^{n+1}\omega}, ac_{\mathfrak s^{n+1}\omega}, ad_{\mathfrak s^{n+1}\omega}\}$, then the substitution $\zeta_{\omega_n}$ can be applied to $g$ and the resulting image in $G_{\mathfrak s^n\omega}$ does not depend on the choice of the representing word.”
--
--   The statement is the negation of this claim as printed, for every $\omega$ in the space $\Omega$ of all strings and for words without inverses. The corrected claim, under a hypothesis on the tail of $\omega$, is the milestone `ErschlerZheng.evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 15, the substitutions on group elements, as printed (fails for a constant tail)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem not_forall_evalWord_zetaWord_congr :
    ¬ ∀ (ω : ℕ → Fin 3) (n : ℕ) (w₁ w₂ : List APair),
      evalWord ω (n + 1) (w₁.flatMap APair.toWord) = evalWord ω (n + 1) (w₂.flatMap APair.toWord) →
        evalWord ω n ((zetaWord (ω n) w₁).flatMap APair.toWord) =
          evalWord ω n ((zetaWord (ω n) w₂).flatMap APair.toWord) := by
  sorry

end ErschlerZheng
