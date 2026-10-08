-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_lemma_2a
-- name    : AdaptiveStepIPM.PredCorr.lemma_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:31.815479+00:00
-- url     : https://prove2.me/theorems/991ffc18-2ce4-4f3d-a648-775cd4889a4f
-- title:
--   Lemma 2(a) — predictor residual identity
-- statement:
--   For an interior feasible pair $(x,s)$ with $n\ge1$, let $\mu=x^Ts/n$ and form the scaled residual $r$ of (6) with $\gamma=0$. Then
--
--   $$\|r\|_2^2=n\mu.$$
--
--   This identity converts the Lemma 1 bound into a bound in the duality measure at the predictor step.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 5, Lemma 2(a)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 2(a), printed p. 5. -/
theorem lemma_2a {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (hxs : F0 A b c x s) :
    (l2Norm (scaledR x s 0)) ^ 2 = (n : ℝ) * mu x s := by sorry

end AdaptiveStepIPM.PredCorr
