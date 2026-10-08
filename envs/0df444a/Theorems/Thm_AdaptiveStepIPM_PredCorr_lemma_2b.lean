-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_lemma_2b
-- name    : AdaptiveStepIPM.PredCorr.lemma_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:24:30.685832+00:00
-- url     : https://prove2.me/theorems/61ef618f-921b-4335-be20-c6d62ff0ea1f
-- title:
--   Lemma 2(b) — corrector residual bound
-- statement:
--   Let $0<\beta<1$ and $(x,s)\in N_2(\beta)$. For the scaled residual $r$ of (6) at $\gamma=1$,
--
--   $$\|r\|_2^2\le\frac{\beta^2\mu}{1-\beta}.$$
--
--   This bounds the full corrector direction starting from the outer neighborhood.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 5, Lemma 2(b)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 2(b), printed p. 5. -/
theorem lemma_2b {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hxs : N2 A b c β x s) :
    (l2Norm (scaledR x s 1)) ^ 2 ≤ β ^ 2 * mu x s / (1 - β) := by sorry

end AdaptiveStepIPM.PredCorr
