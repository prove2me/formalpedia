-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_lemma_2c
-- name    : AdaptiveStepIPM.WideNbhd.lemma_2c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:03.866453+00:00
-- url     : https://prove2.me/theorems/3935141c-c469-4035-acff-a9e509a95375
-- title:
--   Lemma 2(c) — in $\mathcal N^-_\infty(\beta)$, $\|r\|^2\le n\mu$; in $\mathcal N_\infty(\beta)$, $\|r\|_\infty^2\le(1+\beta)\mu$
-- statement:
--   Let $\beta\in(0,1)$ and $\gamma\in(0,1)$ with $\gamma\le 2(1-\beta)$. For a pair $(x,s)$ let $\mu = x^Ts/n$ and $r = (XS)^{-1/2}(\gamma\mu e - Xs)$, that is $r_j = (\gamma\mu - x_js_j)/\sqrt{x_js_j}$.
--
--   1. If $(x,s)\in\mathcal N^-_\infty(\beta)$, then $\|r\|^2\le n\mu$ (Euclidean norm).
--   2. If $(x,s)\in\mathcal N_\infty(\beta)$, then for each $j$
--   $$
--   \sqrt{1-\beta}\sqrt\mu \;\ge\; \Big(\frac{\gamma}{\sqrt{1-\beta}}-\sqrt{1-\beta}\Big)\sqrt\mu \;\ge\; r_j \;\ge\; \Big(\frac{\gamma}{\sqrt{1+\beta}}-\sqrt{1+\beta}\Big)\sqrt\mu \;\ge\; -\sqrt{1+\beta}\sqrt\mu,
--   $$
--   so $\|r\|_\infty^2 \le (1+\beta)\mu$.
--
--   Combined with Lemma 1(c), part 1 bounds the second-order term by $n\mu/4$ in the wide neighbourhood, which is what gives the $O(nt)$ bound of Theorem 2.
--
--   **Formalization Note** The four inequalities of the chain are stated separately for each coordinate $j$, together with the conclusion on $\|r\|_\infty^2$. The standing condition $n\ge1$ (so that $\mu$ is defined) is a hypothesis.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 6, Lemma 2(c)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Lemma 2(c) of Mizuno–Todd–Ye (p. 6): let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`, `μ = xᵀs/n` and
`r = (XS)^{-0.5}(γμe − Xs)`. If `(x, s) ∈ N_∞⁻(β)` then `‖r‖² ≤ nμ`. Moreover, if
`(x, s) ∈ N_∞(β)` then for each `j`
`√(1−β)√μ ≥ (γ/√(1−β) − √(1−β))√μ ≥ r_j ≥ (γ/√(1+β) − √(1+β))√μ ≥ −√(1+β)√μ`,
so `‖r‖²_∞ ≤ (1 + β)μ`. -/
theorem lemma_2c {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) :
    ((x, s) ∈ NinfMinus A b c β → norm2 (rvec γ x s) ^ 2 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s) ∧
      ((x, s) ∈ Ninf A b c β →
        (∀ j, (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ≤
              Real.sqrt (1 - β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ∧
            rvec γ x s j ≤ (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ∧
            (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ≤ rvec γ x s j ∧
            -(Real.sqrt (1 + β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s)) ≤
              (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s)) ∧
        normInf (rvec γ x s) ^ 2 ≤ (1 + β) * AdaptiveStepIPM.PredCorr.mu x s) := by sorry

end AdaptiveStepIPM.WideNbhd
