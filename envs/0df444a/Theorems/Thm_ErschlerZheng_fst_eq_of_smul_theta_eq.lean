-- Prove2me | Theorems.Thm_ErschlerZheng_fst_eq_of_smul_theta_eq
-- name    : ErschlerZheng.fst_eq_of_smul_theta_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T05:40:30.346267+00:00
-- url     : https://prove2.me/theorems/a402c9a8-d9f2-4f0e-8afd-048811b3ef3d
-- title:
--   Lemma 7.15 — for x of level n + D + 1, x · θ_n(ε, γ) determines ε
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), let $D$ divide $n$, and let $x$ be a vertex of length $n + D + 1$. If $(\boldsymbol\epsilon, \boldsymbol\gamma), (\tilde{\boldsymbol\epsilon}, \tilde{\boldsymbol\gamma}) \in \Lambda_n$ (`LambdaN`) satisfy $x \cdot \theta_n(\boldsymbol\epsilon, \boldsymbol\gamma) = x \cdot \theta_n(\tilde{\boldsymbol\epsilon}, \tilde{\boldsymbol\gamma})$ (`theta`), then $\boldsymbol\epsilon = \tilde{\boldsymbol\epsilon}$.
--
--   Erschler and Zheng, p. 44, Lemma 7.15: “Let $x \in \mathsf L_{n+D+1}$. Suppose $(\epsilon_i, \gamma_i)_{i=1}^n, (\tilde\epsilon_i, \tilde\gamma_i)_{i=1}^n \in \Lambda_n$ are such that $x \cdot \gamma_n^{\epsilon_n} \ldots \gamma_1^{\epsilon_1} = x \cdot \tilde\gamma_n^{\tilde\epsilon_n} \ldots \tilde\gamma_1^{\tilde\epsilon_1}$. Then $\epsilon_i = \tilde\epsilon_i$ for all $1 \leqslant i \leqslant n$.”
--
--   $\theta_n(\boldsymbol\epsilon, \boldsymbol\gamma) = \gamma_n^{\epsilon_n} \cdots \gamma_1^{\epsilon_1}$ by definition (p. 40). The conclusion concerns $\boldsymbol\epsilon$ only; nothing is claimed about $\boldsymbol\gamma$ and $\tilde{\boldsymbol\gamma}$. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 44, Lemma 7.15

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
open scoped RightActions

namespace ErschlerZheng

theorem fst_eq_of_smul_theta_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (x : List Bool) (hx : x.length = n + D + 1)
    (p q : LambdaN D ω k n) (h : x <• theta D ω k n p = x <• theta D ω k n q) :
    p.1 = q.1 := by
  sorry

end ErschlerZheng
