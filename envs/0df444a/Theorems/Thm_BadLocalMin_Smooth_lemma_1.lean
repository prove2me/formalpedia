-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_lemma_1
-- name    : BadLocalMin.Smooth.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:24.094204+00:00
-- url     : https://prove2.me/theorems/9b2942bb-493d-4da5-a933-e0f2a2faf355
-- title:
--   Lemma 1, p. 20 — vectors orthogonal to a_1, …, a_d and with positive inner product with a_{d+1}, …, a_{L_1}
-- statement:
--   Let $L_1 \le L_2$ and let $\mathbf a_1, \dots, \mathbf a_{L_1} \in \mathbb R^{L_2}$ be linearly independent. Then for every $1 \le d < L_1$ there are linearly independent vectors $\mathbf u_1, \dots, \mathbf u_{L_2 - d} \in \mathbb R^{L_2}$ such that, for every $1 \le l \le L_2 - d$,
--   $$\langle \mathbf u_l, \mathbf a_j\rangle = 0 \quad (1 \le j \le d), \qquad \langle \mathbf u_l, \mathbf a_j\rangle > 0 \quad (d < j \le L_1).$$
--
--   In the proof of Theorem 1 this lemma is applied to the vectors of Assumption 1(b), with the squared rows $X(j,:)\circ X(j,:)$ last, to build the output data.
--
--   **Formalization Note.** Vectors are indexed from 0: $\mathbf a_{j}$ is `a ⟨j - 1, _⟩`, so "$j \le d$" becomes `j.val < d` and "$j > d$" becomes `d ≤ j.val`. The inner product is `dotProduct`.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, p. 20, Lemma 1 (eqs. (24a)–(24b)); proof Appendix F, pp. 46–47

import Mathlib

namespace BadLocalMin.Smooth

/-- Lemma 1 (p. 20). Vectors are indexed from 0: the paper's a₁, …, a_{L₁} are `a 0`, …,
`a (L1 - 1)`, so "1 ≤ j ≤ d" is `j.val < d` and "d < j ≤ L₁" is `d ≤ j.val`. -/
theorem lemma_1 (L1 L2 d : ℕ) (hL : L1 ≤ L2) (a : Fin L1 → Fin L2 → ℝ)
    (ha : LinearIndependent ℝ a) (hd1 : 1 ≤ d) (hdL : d < L1) :
    ∃ u : Fin (L2 - d) → Fin L2 → ℝ, LinearIndependent ℝ u ∧
      ∀ l j, (j.val < d → u l ⬝ᵥ a j = 0) ∧ (d ≤ j.val → 0 < u l ⬝ᵥ a j) := by sorry

end BadLocalMin.Smooth
