-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_proposition_11
-- name    : EquilibriumExperiment.Gradient.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:30.859651+00:00
-- url     : https://prove2.me/theorems/4a11053a-ce90-4852-ac48-9c788f4f91a9
-- title:
--   Proposition 11, p. 37 — μ^{(n)}(p, ζ) and q^{(n)}(p, ζ) are twice differentiable in ζ, flat at ζ = 0, with uniformly bounded second derivatives
-- statement:
--   Under the standing assumptions, fix a payment $p > 0$, and for $n \ge 1$ write $\mu^{(n)}(p,\zeta) = \mu^{(n)}(\pi_{p,\zeta})$ for the equilibrium under $\zeta$-perturbed payments $p \pm \zeta$ and $q^{(n)}(p,\zeta) = q^{(n)}(\mu^{(n)}(p,\zeta))$. Then:
--   1. for every $n \ge 1$, $\zeta \mapsto \mu^{(n)}(p,\zeta)$ and $\zeta \mapsto q^{(n)}(p,\zeta)$ are twice differentiable on $(-p,p)$;
--   2. for every $n \ge 1$,
--   $$\frac{\partial}{\partial\zeta}\mu^{(n)}(p,\zeta)\Big|_{\zeta=0} = \frac{\partial}{\partial\zeta}q^{(n)}(p,\zeta)\Big|_{\zeta=0} = 0;$$
--   3. there exist $\alpha_0 > 0$ and $C$ such that for all $n \ge 1$ and all $\zeta_0 \in (0,\alpha_0)$,
--   $$\Bigl|\frac{\partial^2}{\partial\zeta^2}\mu^{(n)}(p,\zeta)\Big|_{\zeta=\zeta_0}\Bigr| \le C, \qquad \Bigl|\frac{\partial^2}{\partial\zeta^2}q^{(n)}(p,\zeta)\Big|_{\zeta=\zeta_0}\Bigr| \le C.$$
--
--   Symmetric perturbations therefore move the equilibrium only at second order in $\zeta$, uniformly in the market size; this is what lets the experiment run at the unperturbed equilibrium up to $O(\zeta^2)$.
--
--   **Formalization Note** The paper's $n \in \mathbb N$ is read as $n \ge 1$ (the system with no supplier is excluded). $\zeta$ ranges over $(-p,p)$ so that the derivative at $\zeta = 0$ is two-sided; $\pi_{p,-\zeta} = \pi_{p,\zeta}$, and all payments stay positive. "Twice differentiable" is formalized as differentiability of the function and of its derivative on $(-p,p)$, not as continuity of the second derivative. The existential constant is named $\alpha_0$ to avoid a clash with Theorem 6's exponent $\alpha$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 37, Proposition 11; proof in Appendix B.4

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem proposition_11 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) :
    (∀ n : ℕ, 1 ≤ n →
      DifferentiableOn ℝ (fun ζ : ℝ => M.muN n (perturbLaw p ζ)) (Set.Ioo (-p) p) ∧
      DifferentiableOn ℝ (deriv fun ζ : ℝ => M.muN n (perturbLaw p ζ)) (Set.Ioo (-p) p) ∧
      DifferentiableOn ℝ (fun ζ : ℝ => M.q n (M.muN n (perturbLaw p ζ))) (Set.Ioo (-p) p) ∧
      DifferentiableOn ℝ (deriv fun ζ : ℝ => M.q n (M.muN n (perturbLaw p ζ)))
        (Set.Ioo (-p) p)) ∧
    (∀ n : ℕ, 1 ≤ n →
      deriv (fun ζ : ℝ => M.muN n (perturbLaw p ζ)) 0 = 0 ∧
      deriv (fun ζ : ℝ => M.q n (M.muN n (perturbLaw p ζ))) 0 = 0) ∧
    (∃ α₀ : ℝ, 0 < α₀ ∧ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ζ₀ ∈ Set.Ioo (0 : ℝ) α₀,
      |deriv (deriv fun ζ : ℝ => M.muN n (perturbLaw p ζ)) ζ₀| ≤ C ∧
      |deriv (deriv fun ζ : ℝ => M.q n (M.muN n (perturbLaw p ζ))) ζ₀| ≤ C) := by sorry

end EquilibriumExperiment.Gradient
