-- Prove2me | Theorems.Thm_DIGing_Push_relation_49
-- name    : DIGing.Push.relation_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:38.487816+00:00
-- url     : https://prove2.me/theorems/46366663-66e3-4dd9-b1ce-db0f67692d03
-- title:
--   (49), p. 22 — every push-sum weight is positive and ‖V(k)⁻¹‖_max ≤ n^{nB⊖}
-- statement:
--   Let the arc sets $\mathcal A(k)$ satisfy Assumption 6 with constant $\tilde B_\ominus$, put $B_\ominus=2\tilde B_\ominus-1$, and let the mixing matrices $C(k)$ satisfy Assumption 7. Let $\mathbf v(0)=\mathbf 1$ and $\mathbf v(k+1)=C(k)\mathbf v(k)$. Then for every $k\ge0$ and every agent $i$,
--   $$v_i(k)>0\qquad\text{and}\qquad \frac{1}{v_i(k)}\le n^{nB_\ominus}.$$
--   Equivalently, every $V(k)=\operatorname{diag}\{\mathbf v(k)\}$ is invertible and
--   $$\|V^{-1}\|^1_{\max}=\sup_{k\ge0}\|V(k)^{-1}\|_{\max}\le n^{nB_\ominus}.$$
--
--   This bound makes the constant $\|V^{-1}\|^1_{\max}$ of Lemma 15 and Theorem 18 finite. The paper attributes it to Corollary 2(b) of Nedić and Olshevsky (2015).
--
--   **Formalization Note** Assumption 7 includes the disclosed self-weight. The bound is stated entrywise for each $k$ and $i$, which is the same as the bound on the supremum.
-- source:
--   arXiv:1607.03218v3, §5, display (49) and the sentence before it, p. 22

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem relation_49 {n : ℕ} (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ) (h6 : Assumption6 A Bt)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C) :
    ∀ k i, 0 < vSeq C k i ∧ (vSeq C k i)⁻¹ ≤ (n : ℝ) ^ (n * (2 * Bt - 1)) := by sorry

end DIGing.Push
