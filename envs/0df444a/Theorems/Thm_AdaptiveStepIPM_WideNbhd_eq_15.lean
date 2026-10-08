-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_eq_15
-- name    : AdaptiveStepIPM.WideNbhd.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:06.031592+00:00
-- url     : https://prove2.me/theorems/c36bd161-bfa0-4796-bc58-1ab596895848
-- title:
--   (15) — one iteration of Algorithm 2 gives $\mu^{k+1}\le(1-4\beta\gamma(1-\gamma)/n)\mu^k$
-- statement:
--   Let $n\ge1$, $\beta,\gamma\in(0,1)$ with $\gamma\le 2(1-\beta)$, and let $\mathcal N$ be $\mathcal N_\infty(\beta)$ or $\mathcal N^-_\infty(\beta)$. If $(x^+,s^+)$ is obtained from $(x,s)$ by one iteration of Algorithm 2 with neighbourhood $\mathcal N$ and parameter $\gamma$ (a solution $d$ of (2), the largest step $\bar\theta$ keeping $(x(\theta),s(\theta))\in\mathcal N$ on $[0,\bar\theta]$, and $(x^+,s^+) = (x(\bar\theta),s(\bar\theta))$), then with $\mu = x^Ts/n$ and $\mu^+ = (x^+)^Ts^+/n$,
--   $$
--   \mu^+ \;\le\; \Big(1-\frac{4\beta\gamma(1-\gamma)}{n}\Big)\mu .
--   $$
--
--   This is inequality (15): every iteration of Algorithm 2 reduces the duality gap by a factor $1-\Omega(1/n)$, which is the per-iteration content of Theorem 2.
--
--   **Formalization Note** The paper writes (15) as $\mu^{k+1}\le(1-4\beta\gamma(1-\gamma)/n)\mu^k$ along a run; it is stated here for a single iteration, which is how it is used. An iteration includes $(x,s)\in\mathcal N$ (the step $\theta=0$ is admissible).
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 10, proof of Theorem 2, (15)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Inequality (15) in the proof of Theorem 2 of Mizuno–Todd–Ye (p. 10): for `β, γ ∈ (0, 1)` with
`γ ≤ 2(1 − β)` and `N = N_∞(β)` or `N_∞⁻(β)`, one iteration `(x, s) ↦ (x⁺, s⁺)` of Algorithm 2
satisfies `μ⁺ ≤ (1 − 4βγ(1 − γ)/n) μ`, where `μ = xᵀs/n`, `μ⁺ = (x⁺)ᵀs⁺/n`. -/
theorem eq_15 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hN : N = Ninf A b c β ∨ N = NinfMinus A b c β) (x s x' s' : Fin n → ℝ)
    (hstep : Alg2Step A N γ x s x' s') :
    AdaptiveStepIPM.PredCorr.mu x' s' ≤ (1 - 4 * β * γ * (1 - γ) / n) * AdaptiveStepIPM.PredCorr.mu x s := by sorry

end AdaptiveStepIPM.WideNbhd
