-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_contraction
-- name    : AdaptiveStepIPM.PredCorr.contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:49.614987+00:00
-- url     : https://prove2.me/theorems/3036d11a-6852-475c-90c6-cc3d891d9f38
-- title:
--   Proof of Theorem 1 — one-iteration contraction
-- statement:
--   For $n\ge2$, one Algorithm 1 iteration starting from $(x,s)\in N_2(1/4)$ reduces the duality measure according to
--
--   $$\mu^+\le\left(1-8^{-1/4}n^{-1/2}\right)\mu.$$
--
--   This is the per-iteration estimate displayed in the proof of Theorem 1 and drives its termination count.
--
--   **Formalization Note** The bound on $\theta_1$ used in the printed proof fails at $n=1$; this milestone records the range $n\ge2$. Nothing is lost: at $n=1$ the predictor term $Pq$ vanishes, the admissible predictor steps form $[0,1)$ with no greatest element, and Algorithm 1 has no iteration at all.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 9, proof of Theorem 1, contraction display

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- The contraction displayed in the proof of Theorem 1, printed p. 9. -/
theorem contraction {m n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    mu xNext sNext ≤
      (1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))) * mu x s := by sorry

end AdaptiveStepIPM.PredCorr
