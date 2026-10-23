-- Prove2me | Theorems.Thm_DriftLinBandit_BOB_lemma_5
-- name    : DriftLinBandit.BOB.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:00.236396+00:00
-- url     : https://prove2.me/theorems/6d69f20a-36c0-4ddb-a3d6-e0f1fe00140f
-- title:
--   Lemma 5, p. 37 — within a length-w piece the sliding-window potentials are dominated by the restarted ones
-- statement:
--   Let $X_1,X_2,\dots\in\mathbb R^d$ be arbitrary vectors, $\lambda>0$, $w\ge1$ a window size and $T$ a horizon. Write $V_{t-1}=\lambda I+\sum_{s=1\vee(t-w)}^{t-1}X_sX_s^\top$ for the sliding-window Gram matrix and, for a piece index $i$,
--   $$
--   \overline V_{t-1}=\sum_{s=iw+1}^{t-1}X_sX_s^\top+\lambda I \tag{49}
--   $$
--   for the Gram matrix restarted at round $iw+1$. Then for every $i\le\lceil T/w\rceil-1$,
--   $$
--   \sum_{t=iw+1}^{(i+1)w}1\wedge\|X_t\|^2_{V_{t-1}^{-1}}\le\sum_{t=iw+1}^{(i+1)w}1\wedge\|X_t\|^2_{\overline V_{t-1}^{-1}} .
--   $$
--
--   It replaces the elliptical-potential argument of Abbasi-Yadkori et al., which breaks for sliding windows, in the proof of Theorem 3.
--
--   **Formalization Note.** $1\wedge a$ is $\min(1,a)$ and $\|x\|^2_{A^{-1}}=x^\top A^{-1}x$. The condition $i\le\lceil T/w\rceil-1$ is written $i+1\le\lceil T/w\rceil$ over the naturals. The vectors are not required to come from an instance.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, p. 37, Lemma 5 and (49) (Appendix C)

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open Matrix

/-- Lemma 5 (p. 37). For any vectors `X_t`, any `λ > 0`, any window size `w ≥ 1`, any horizon `T`
and any `i ≤ ⌈T/w⌉ − 1`,
`∑_{t=iw+1}^{(i+1)w} 1 ∧ ‖X_t‖²_{V_{t−1}^{−1}} ≤ ∑_{t=iw+1}^{(i+1)w} 1 ∧ ‖X_t‖²_{V̄_{t−1}^{−1}}`,
where `V_{t−1} = λI + ∑_{s=1∨(t−w)}^{t−1} X_s X_sᵀ` is the sliding-window Gram matrix and
`V̄_{t−1} = ∑_{s=iw+1}^{t−1} X_s X_sᵀ + λI` (49). -/
theorem lemma_5 {d : ℕ} (X : ℕ → Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w)
    (T : ℕ) (i : ℕ) (hi : i + 1 ≤ ⌈(T : ℝ) / (w : ℝ)⌉₊) :
    ∑ t ∈ Finset.Icc (i * w + 1) ((i + 1) * w),
        min 1 (X t ⬝ᵥ ((gram lam X (win 1 w t))⁻¹ *ᵥ X t)) ≤
      ∑ t ∈ Finset.Icc (i * w + 1) ((i + 1) * w),
        min 1 (X t ⬝ᵥ ((gram lam X (Finset.Icc (i * w + 1) (t - 1)))⁻¹ *ᵥ X t)) := by sorry

end DriftLinBandit.BOB
