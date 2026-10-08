-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Potential_potential_decrease_per_iteration
-- name    : AdaptiveStepIPM.Potential.potential_decrease_per_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:18.948853+00:00
-- url     : https://prove2.me/theorems/53ba75e8-d6cb-436d-a4c0-199e065c6a06
-- title:
--   Proof of Theorem 3 — each iteration of Algorithm 3 decreases $\psi$ by at least $11n\log\frac{1}{1-\beta}$
-- statement:
--   Let $n \ge 1$, $\beta, \gamma \in (0,1)$ with $\gamma \le 2(1-\beta)$, and
--   $\rho = n + \bigl(\frac{3}{\beta\gamma(1-\gamma)}\log\frac{1}{1-\beta}\bigr)n^2$. Let $(x, s) \in \mathcal N_\infty^-(\beta)$, let $d = (d_x, d_y, d_s)$ solve system (2) at $(x,s)$ with parameter $\gamma$, and let $\bar\theta$ be a step of Algorithm 3: $(x(\bar\theta), s(\bar\theta)) \in \mathcal N_\infty^-(\beta)$ and $\psi(x(\bar\theta), s(\bar\theta)) \le \psi(x(\theta), s(\theta))$ for every real $\theta$ with $(x(\theta), s(\theta)) \in \mathcal N_\infty^-(\beta)$. Then
--   $$
--   \psi(x(\bar\theta), s(\bar\theta)) - \psi(x, s) \le -11n\log\frac{1}{1-\beta}.
--   $$
--
--   Since $\rho - n$ is of order $n^2$ and a total decrease of order $n^2t$ suffices, this fixed decrease per iteration is what yields the $O(nt)$ bound of Theorem 3.
--
--   **Formalization Note** The paper derives this from (16) and $\theta_2^- \ge 4\beta\gamma/n$. For $n \ge 2$ the latter holds because $4\beta\gamma \le 2 \le n$ under $\gamma \le 2(1-\beta)$. For $n = 1$ it can fail, but then no step $\bar\theta$ of Algorithm 3 exists ($\mathcal N_\infty^-(\beta) = \mathcal F^0$, $x(\theta)s(\theta) = (1-(1-\gamma)\theta)\mu$ and $\psi = (\rho-1)\log(x(\theta)s(\theta))$ is unbounded below on $[0, 1/(1-\gamma))$), so the statement holds there with no extra hypothesis; $n \ge 1$ is kept as on the page.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 12, proof of Theorem 3 (after (16))

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **Proof of Theorem 3, p. 12.** Under the hypotheses of (16),
one iteration of Algorithm 3 decreases the potential by at least `11n log(1/(1 − β))`:
`ψ(x(θ̄), s(θ̄)) − ψ(x, s) ≤ −11n log(1/(1 − β))`. -/
theorem potential_decrease_per_iteration {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
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
      -(11 * (n : ℝ) * Real.log (1 / (1 - β))) := by sorry

end AdaptiveStepIPM.Potential
