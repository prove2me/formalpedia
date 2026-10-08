-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_lemma_1a
-- name    : AdaptiveStepIPM.PredCorr.lemma_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:54.073159+00:00
-- url     : https://prove2.me/theorems/00453f27-8afe-4fa9-94cd-009f7b15c743
-- title:
--   Lemma 1(a) — Euclidean bound on the second-order term
-- statement:
--   Let $(x,s)\in F^0$, let $0\le\gamma\le1$, and let $(d_x,d_y,d_s)$ solve system (2). With the scaled vectors $p,q,r$ of (6) and $P=\operatorname{diag}(p)$,
--
--   $$\|Pq\|_2\le\frac{\sqrt2}{4}\|r\|_2^2.$$
--
--   This inequality bounds the nonlinear term in the centrality equation and is used for both predictor and corrector steps.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 5, Lemma 1(a), equation (9)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 1(a), equation (9), printed p. 5. -/
theorem lemma_1a {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx ds : Fin n → ℝ) (dy : Fin m → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hxs : F0 A b c x s)
    (hd : SearchDirection A x s γ dx dy ds) :
    l2Norm (Pq x s dx ds) ≤
      (Real.sqrt 2 / 4) * (l2Norm (scaledR x s γ)) ^ 2 := by sorry

end AdaptiveStepIPM.PredCorr
