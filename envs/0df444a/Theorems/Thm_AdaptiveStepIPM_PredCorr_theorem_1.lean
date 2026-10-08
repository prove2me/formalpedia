-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_theorem_1
-- name    : AdaptiveStepIPM.PredCorr.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:26.759989+00:00
-- url     : https://prove2.me/theorems/ae2f290e-9ac5-4ba3-b12b-e23ba5e11e6d
-- title:
--   Theorem 1 — predictor-corrector termination in O(√n·t) iterations
-- statement:
--   Let $n\ge1$ and let $t$ be a real precision parameter. Start Algorithm 1 at $(x^0,s^0)\in N_2(1/4)$ with $(x^0)^Ts^0\le2^t$. At every iteration whose gap is greater than $2^{-t}$, take the predictor step at $\gamma=0$ to the greatest step whose entire prefix lies in $N_2(1/2)$, followed by one full corrector step at $\gamma=1$. Then for some iteration $k$,
--
--   $$k\le\left\lceil 2(\log 2)8^{1/4}\sqrt n\,t\right\rceil,\qquad (x^k)^Ts^k\le2^{-t}.$$
--
--   Thus Algorithm 1 attains precision $t$ in the $O(\sqrt n\,t)$ iteration scale stated in Theorem 1.
--
--   **Formalization Note** The explicit ceiling is the count yielded by the paper's contraction factor $1-8^{-1/4}n^{-1/2}$, with natural logarithm. The run relation uses an attained greatest predictor step. At inputs where no greatest step exists, such as $n=1$, it has no successor; the statement keeps the report's $n\ge1$ range, although those runs cannot continue above the stopping threshold. No sign condition on $t$ is imposed: for $t\le0$ the starting pair already satisfies $(x^0)^Ts^0\le2^t\le2^{-t}$ and the bound is met at $k=0$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 8–9, Theorem 1 and proof

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Theorem 1, printed p. 8, with the explicit count from its proof. -/
theorem theorem_1 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (t : ℝ) (x s : ℕ → Fin n → ℝ)
    (hinit : N2 A b c (1 / 4) (x 0) (s 0))
    (hgap : x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t)
    (hrun : ∀ k : ℕ, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k →
      Alg1Step A b c (x k) (s k) (x (k + 1)) (s (k + 1))) :
    ∃ k : ℕ,
      k ≤ ⌈2 * Real.log 2 * (8 : ℝ) ^ (1 / 4 : ℝ) *
        Real.sqrt (n : ℝ) * t⌉₊ ∧
      x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.PredCorr
