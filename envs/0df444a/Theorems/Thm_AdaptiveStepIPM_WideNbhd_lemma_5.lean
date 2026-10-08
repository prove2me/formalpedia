-- Prove2me | Theorems.Thm_AdaptiveStepIPM_WideNbhd_lemma_5
-- name    : AdaptiveStepIPM.WideNbhd.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:55.631496+00:00
-- url     : https://prove2.me/theorems/a3ca0d8d-d9b6-4ef7-ae6c-c9f19e1f50cf
-- title:
--   Lemma 5 — the step length of Algorithm 2 is at least $\theta_2 = \min\{1, \beta\gamma\mu/\|Pq\|_\infty\}$ (resp. $\theta_2^-$)
-- statement:
--   Let $\beta,\gamma\in(0,1)$, let $\mathcal N$ be $\mathcal N_\infty(\beta)$ or $\mathcal N^-_\infty(\beta)$, let $(x,s)\in\mathcal N$ with $\mu = x^Ts/n$, let $(d_x,d_y,d_s)$ solve (2) at $(x,s)$ with parameter $\gamma$, and let $p,q$ be the scaled vectors (6). Put
--   $$
--   \theta_2 := \min\Big\{1,\frac{\beta\gamma\mu}{\|Pq\|_\infty}\Big\},\qquad
--   \theta_2^- := \min\Big\{1,\frac{\beta\gamma\mu}{\|Pq\|^-_\infty}\Big\}.
--   $$
--
--   1. If $\mathcal N = \mathcal N_\infty(\beta)$, then $(x(\theta),s(\theta)) = (x+\theta d_x, s+\theta d_s)\in\mathcal N_\infty(\beta)$ for every $\theta\in[0,\theta_2]$; hence the largest admissible step $\bar\theta$ of Algorithm 2 satisfies $\bar\theta\ge\theta_2$.
--   2. If $\mathcal N = \mathcal N^-_\infty(\beta)$, the same holds with $\theta_2^-$ in place of $\theta_2$.
--
--   Since one iteration reduces the duality measure to $(1-\bar\theta(1-\gamma))\mu$, a lower bound on $\bar\theta$ is a guaranteed decrease of the duality gap.
--
--   **Formalization Note** When the norm in a denominator is $0$, the quotient is $+\infty$ and the minimum is $1$; Lean's division by zero gives $0$, so this case is defined as $1$ explicitly. The admissibility of every $\theta\in[0,\theta_2]$ is the statement the paper's proof establishes; the bound on $\bar\theta$ is stated for every greatest admissible step. The standing condition $n\ge1$ is a hypothesis.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 10, Lemma 5

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- Lemma 5 of Mizuno–Todd–Ye (p. 10): let `β, γ ∈ (0, 1)`, `(x, s)` in the neighbourhood `N`,
`d` a solution of (2) at `(x, s)` with `γ`, `μ = xᵀs/n` and `p, q` as in (6).
If `N = N_∞(β)`, every `θ ∈ [0, θ₂]` with `θ₂ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖_∞}` keeps `(x(θ), s(θ)) ∈ N`, so
the largest admissible `θ̄` satisfies `θ̄ ≥ θ₂`; likewise for `N = N_∞⁻(β)` with
`θ₂⁻ = min{1, βγμ/‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞}`. (The minimum is `1` when the norm is `0`.) -/
theorem lemma_5 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x s : Fin n → ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsDirection A x s γ dx dy ds) :
    ((x, s) ∈ Ninf A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ Ninf A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (Ninf A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) ∧
      ((x, s) ∈ NinfMinus A b c β →
        (∀ θ ∈ Set.Icc (0 : ℝ) (stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds))),
            (x + θ • dx, s + θ • ds) ∈ NinfMinus A b c β) ∧
        ∀ θbar, IsGreatest (admissibleSteps (NinfMinus A b c β) x s dx ds) θbar →
          stepBound β γ (AdaptiveStepIPM.PredCorr.mu x s) (normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds)) ≤ θbar) := by sorry

end AdaptiveStepIPM.WideNbhd
