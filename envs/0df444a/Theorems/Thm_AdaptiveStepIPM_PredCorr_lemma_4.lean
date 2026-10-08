-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_lemma_4
-- name    : AdaptiveStepIPM.PredCorr.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:44.218984+00:00
-- url     : https://prove2.me/theorems/13c091c5-1da6-4c9d-8b58-0f510d469e51
-- title:
--   Lemma 4 — predictor step lower bound
-- statement:
--   At a pair $(x,s)\in N_2(1/4)$, let a predictor direction solve (2) with $\gamma=0$, and let $\bar\theta$ be the greatest step whose entire prefix stays in $N_2(1/2)$. Define $\theta_1=\min\{1/2,\sqrt{\mu/(8\|Pq\|_2)}\}$ when $\|Pq\|_2>0$, and $\theta_1=1/2$ otherwise. Then
--
--   $$\bar\theta\ge\theta_1,$$
--
--   and every step $0\le\theta\le\theta_1$ is admissible. The bound supplies a guaranteed decrease of the duality measure at a predictor step.
--
--   **Formalization Note** The zero-denominator branch is the limiting value of the printed expression, avoiding Lean's totalized division by zero.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 8, Lemma 4

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 4, printed p. 8: the lower bound and its admissibility. -/
theorem lemma_4 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx ds : Fin n → ℝ) (dy : Fin m → ℝ) (θbar : ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hd : SearchDirection A x s 0 dx dy ds)
    (hmax : IsGreatest {θ : ℝ | PredictorAdmissible A b c x s dx ds θ} θbar) :
    PredictorAdmissible A b c x s dx ds (theta1 x s dx ds) ∧
      theta1 x s dx ds ≤ θbar := by sorry

end AdaptiveStepIPM.PredCorr
