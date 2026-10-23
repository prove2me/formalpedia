-- Prove2me | Theorems.Thm_AssortRotation_Concealment_lemma_1
-- name    : AssortRotation.Concealment.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:17.648131+00:00
-- url     : https://prove2.me/theorems/ae743771-2a40-4c52-9405-f19c1759ae27
-- title:
--   Lemma 1, p. 11 — buying greedily in decreasing price-adjusted valuation maximizes the consumer's utility
-- statement:
--   Consider a fixed assortment of $M$ products with prices $p_1,\dots,p_M$ and realized shocks $x_1,\dots,x_M$. Let $v$ be a nonnegative, decreasing marginal-utility sequence, and let $\sigma$ be a permutation of the products such that
--   $$
--   x_{\sigma(1)}-p_{\sigma(1)}\ \ge\ x_{\sigma(2)}-p_{\sigma(2)}\ \ge\ \cdots\ \ge\ x_{\sigma(M)}-p_{\sigma(M)} .
--   $$
--   Let $D^f=|\{j: v(j-1)+x_{\sigma(j)}-p_{\sigma(j)}\ge 0\}|$. Then buying the products $\sigma(1),\dots,\sigma(D^f)$ maximizes the consumer's utility (3): for every subset $S$ of the products,
--   $$
--   u(S)\ \le\ u\big(\{\sigma(1),\dots,\sigma(D^f)\}\big),\qquad u(S)=\sum_{j\in S}(x_j-p_j)+\sum_{j=0}^{|S|-1}v(j).
--   $$
--
--   This characterizes the consumer's purchase under a fixed assortment, and it is what justifies the revenue formula (4).
--
--   **Formalization Note.** Positions are 0-based in Lean, so the condition reads $v(j)+x_{\sigma(j)}-p_{\sigma(j)}\ge 0$ for $j=0,\dots,M-1$. The printed policy $\pi^f_i=\mathbb 1\{\sigma(i)\le D^f\}$ has an index slip. The proof (p. 35) and the surrounding text buy the product in position $i$ iff $i\le D^f$, and the statement formalizes that.
-- source:
--   Ferreira & Goh, HBS Working Paper 17-041 (2020 revision), p. 11, Lemma 1 (proof p. 35); utility (3) p. 8; Definition 1 p. 10

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

namespace AssortRotation.Concealment

/-- Lemma 1, p. 11 (proof p. 35). For a fixed assortment of `M` products with prices `p`
and realized shocks `x`, let `σ` order the products by decreasing price-adjusted valuation
`x − p` (Definition 1). With 0-based positions, `D = #{j : v(j) + x_{σ j} − p_{σ j} ≥ 0}`
(the paper's `D^f`, whose 1-based condition is `v(j−1) + X_{σ(j)} − p_{σ(j)} ≥ 0`). Buying
the products at the first `D` positions of σ maximizes the utility (3) over all subsets. -/
theorem lemma_1 {M : ℕ} (v : ℕ → ℝ) (hv : MarginalUtility v) (p x : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (hσ : Antitone (fun i => x (σ i) - p (σ i))) (S : Finset (Fin M)) :
    utility v p x S ≤
      utility v p x
        ((Finset.univ.filter (fun j : Fin M =>
            (j : ℕ) < (Finset.univ.filter (fun i : Fin M =>
              0 ≤ v i + x (σ i) - p (σ i))).card)).map σ.toEmbedding) := by sorry

end AssortRotation.Concealment
