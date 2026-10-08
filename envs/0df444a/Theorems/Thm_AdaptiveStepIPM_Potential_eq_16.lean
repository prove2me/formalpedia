-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Potential_eq_16
-- name    : AdaptiveStepIPM.Potential.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:27.524007+00:00
-- url     : https://prove2.me/theorems/d64ca740-6f0c-47c2-ba2c-0ed6282e00e2
-- title:
--   (16) — one step of Algorithm 3 decreases $\psi$ by at least $(3n^2\theta_2^-/(\beta\gamma) - n)\log\frac{1}{1-\beta}$
-- statement:
--   Let $n \ge 1$, $\beta, \gamma \in (0,1)$ with $\gamma \le 2(1-\beta)$, and
--   $\rho = n + \bigl(\frac{3}{\beta\gamma(1-\gamma)}\log\frac{1}{1-\beta}\bigr)n^2$. Let $(x, s) \in \mathcal N_\infty^-(\beta)$ with $\mu = x^Ts/n$, let $d = (d_x, d_y, d_s)$ be a solution of system (2) at $(x,s)$ with parameter $\gamma$, and let $x(\theta) = x + \theta d_x$, $s(\theta) = s + \theta d_s$. Let $\bar\theta$ be a step of Algorithm 3: $(x(\bar\theta), s(\bar\theta)) \in \mathcal N_\infty^-(\beta)$ and $\psi(x(\bar\theta), s(\bar\theta)) \le \psi(x(\theta), s(\theta))$ for every real $\theta$ with $(x(\theta), s(\theta)) \in \mathcal N_\infty^-(\beta)$. With $\theta_2^- = \min\{1, \beta\gamma\mu/\|Pq\|_\infty^-\}$ as in Lemma 5,
--   $$
--   \psi(x(\bar\theta), s(\bar\theta)) - \psi(x, s) \le -\Bigl(\frac{3n^2\theta_2^-}{\beta\gamma} - n\Bigr)\log\frac{1}{1-\beta}. \tag{16}
--   $$
--
--   This is the potential-decrease estimate behind Theorem 3 and Corollary 3: a large step bound $\theta_2^-$, i.e. a small second-order term $Pq$, gives a large decrease of $\psi$.
--
--   **Formalization Note** $\psi$ is `LinearOptimization.interiorPointPotential` with parameter $\rho$; all points at which it is evaluated lie in $\mathcal N_\infty^-(\beta)$, so are strictly positive. $\theta_2^- := 1$ when $\|Pq\|_\infty^- = 0$. The statement is self-contained: the admissibility of $\theta_2^-$ (Lemma 5 of the paper) is part of what is to be proved.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 12, proof of Theorem 3, (16)

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **(16), proof of Theorem 3, p. 12.** Let `β, γ ∈ (0, 1)` with `γ ≤ 2(1 − β)`,
`ρ = n + (3/(βγ(1 − γ)) log(1/(1 − β))) n²`, `(x, s) ∈ N_∞⁻(β)`, `d` a solution of (2) at
`(x, s)` with `γ`, and `θ̄` an Algorithm 3 step: `(x(θ̄), s(θ̄)) ∈ N_∞⁻(β)` and `θ̄` minimises
`ψ(x(θ), s(θ))` over all `θ` with `(x(θ), s(θ)) ∈ N_∞⁻(β)`. Then
`ψ(x(θ̄), s(θ̄)) − ψ(x, s) ≤ −(3n²θ₂⁻/(βγ) − n) log(1/(1 − β))`. -/
theorem eq_16 {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θbar : ℝ)
    (hθN : InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar))
    (hθmin : ∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θ) (lineStep s ds θ)) :
    LinearOptimization.interiorPointPotential (rho n β γ)
          (lineStep x dx θbar) (lineStep s ds θbar) -
        LinearOptimization.interiorPointPotential (rho n β γ) x s ≤
      -(3 * (n : ℝ) ^ 2 * theta2Minus β γ x s dx ds / (β * γ) - n) *
        Real.log (1 / (1 - β)) := by sorry

end AdaptiveStepIPM.Potential
