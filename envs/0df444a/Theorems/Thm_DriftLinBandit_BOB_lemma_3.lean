-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_lemma_3
-- name    : DriftLinBandit.BOB.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:55.388524+00:00
-- url     : https://prove2.me/theorems/435704ac-4bae-44c5-a7c2-c6b72dad706e
-- title:
--   Lemma 3, p. 35 — under Assumption 1 the drift term of the sliding-window estimator is at most the window's variation
-- statement:
--   Let $D_1,\dots,D_T\subseteq\mathbb R^d$ and $\theta_1,\dots,\theta_T$ be an instance satisfying Assumption 1 (every action is a multiple of one vector of a fixed orthonormal basis), let $X_s\in D_s$ be arbitrary actions, $\lambda>0$, and $w\ge1$ a window size. For a round $t\in[T]$ put $V_{t-1}=\lambda I+\sum_{s=1\vee(t-w)}^{t-1}X_sX_s^\top$. Then
--   $$
--   \Big\|V_{t-1}^{-1}\sum_{s=1\vee(t-w)}^{t-1}X_sX_s^\top(\theta_s-\theta_t)\Big\|_2\le\sum_{s=1\vee(t-w)}^{t-1}\|\theta_s-\theta_{s+1}\|_2 .
--   $$
--
--   This bounds the bias of the sliding-window estimator caused by the drift of $\theta$, the first term of the decomposition (34) of $\hat\theta_t-\theta_t$.
--
--   **Formalization Note.** $X_sX_s^\top v$ is written $\langle X_s,v\rangle X_s$. Assumption 1 is a hypothesis: §5 makes it standing (p. 10), and the inequality fails for actions in general position.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 35, Lemma 3 (Appendix B); Assumption 1, p. 10

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open Matrix

/-- Lemma 3 (p. 35). Under Assumption 1, for any actions `X_s ∈ D_s`, any `λ > 0`, any window size
`w ≥ 1` and any round `t ∈ [T]`,
`‖V_{t−1}^{−1} ∑_{s=1∨(t−w)}^{t−1} X_s X_sᵀ (θ_s − θ_t)‖₂ ≤ ∑_{s=1∨(t−w)}^{t−1} ‖θ_s − θ_{s+1}‖₂`,
where `V_{t−1} = λI + ∑_{s=1∨(t−w)}^{t−1} X_s X_sᵀ`. -/
theorem lemma_3 {d : ℕ} (I : Instance d) (hA : Assumption1 I) (lam : ℝ) (hlam : 0 < lam)
    (w : ℕ) (hw : 1 ≤ w) (X : ℕ → Fin d → ℝ) (hX : ∀ s ∈ Finset.Icc 1 I.T, X s ∈ I.D s)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 I.T) :
    l2 ((gram lam X (win 1 w t))⁻¹ *ᵥ
        ∑ s ∈ win 1 w t, (X s ⬝ᵥ (I.θ s - I.θ t)) • X s) ≤
      ∑ s ∈ win 1 w t, l2 (I.θ s - I.θ (s + 1)) := by sorry

end DriftLinBandit.BOB
