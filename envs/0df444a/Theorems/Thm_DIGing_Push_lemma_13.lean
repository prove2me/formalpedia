-- Prove2me | Theorems.Thm_DIGing_Push_lemma_13
-- name    : DIGing.Push.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:53.873871+00:00
-- url     : https://prove2.me/theorems/0c140f49-5c1e-44fe-85ae-4528a2060b97
-- title:
--   Lemma 13, p. 22 — B-step consensus contraction ‖R̃_B(k)b‖_L ≤ δ‖b‖_L for k ≥ B − 1
-- statement:
--   Let $n\ge2$, let the arc sets satisfy Assumption 6 with constant $\tilde B_\ominus$, $B_\ominus=2\tilde B_\ominus-1$, and let $C(k)$ satisfy Assumption 7. Let $B$ be an integer with $B\ge B_\ominus$ and
--   $$\delta=Q_1\big(1-\tilde\tau^{nB_\ominus}\big)^{\frac{B-1}{nB_\ominus}}<1,\qquad Q_1=2n\,\frac{1+\tilde\tau^{-nB_\ominus}}{1-\tilde\tau^{nB_\ominus}},\qquad \tilde\tau=\frac1{n^{2+nB_\ominus}}.$$
--   Then for every $k\ge B-1$ and every $\mathbf b\in\mathbb R^{n\times p}$, the matrix $\mathbf a=\tilde R_B(k)\mathbf b=V(k+1)^{-1}C_B(k)V(k+1-B)\mathbf b$ satisfies
--   $$\|\mathbf a\|_{\mathbf L}\le\delta\,\|\mathbf b\|_{\mathbf L},$$
--   where $\|\mathbf a\|_{\mathbf L}=\|(I-\frac1n\mathbf 1\mathbf 1^\top)\mathbf a\|_F$.
--
--   This is the directed analogue of Lemma 2: after $B$ steps the products of the matrices $\tilde R(k)$ contract the distance to consensus by the factor $\delta$. It is used in Lemmas 15 and 16.
--
--   **Formalization Note** $\tilde R_B(k)$ is the product $\tilde R(k)\cdots\tilde R(k-B+1)$, which telescopes to $V(k+1)^{-1}C_B(k)V(k+1-B)$. Assumption 7 includes the disclosed self-weight. The hypothesis $n\ge2$ is added: at $n=1$, $\tilde\tau=1$ and $Q_1$ has a zero denominator on the page.
-- source:
--   arXiv:1607.03218v3, Lemma 13 and (50), p. 22

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem lemma_13 {n p : ℕ} (hn : 2 ≤ n) (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ)
    (h6 : Assumption6 A Bt) (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C)
    (B : ℕ) (hB : 2 * Bt - 1 ≤ B) (hδ : deltaPush n (2 * Bt - 1) B < 1) :
    ∀ k, B - 1 ≤ k → ∀ b : DIGing.Undir.Stack n p,
      DIGing.Undir.frob (DIGing.Undir.cons (DIGing.Undir.mix (prodR C B k) b)) ≤ deltaPush n (2 * Bt - 1) B * DIGing.Undir.frob (DIGing.Undir.cons b) := by sorry

end DIGing.Push
