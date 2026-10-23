-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_eq_A9
-- name    : EquilibriumExperiment.Gradient.eq_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:33.984117+00:00
-- url     : https://prove2.me/theorems/12669e33-5a76-40f4-be6e-cb2c2814cd9e
-- title:
--   (A.9), proof of Theorem 6, p. 38 — |ζ⁻¹ Cov_n[Z_i, ε_i] − Δ_a^{(n)}(p)| ≤ ζC uniformly in n
-- statement:
--   Under the standing assumptions, fix a payment $p > 0$. For $\zeta \in (0,p)$ and $n \ge 1$ let $q_\ast = q^{(n)}(\mu^{(n)}(p,\zeta))$ be the matching rate at the perturbed equilibrium, and
--   $$\mathrm{Cov}_n[Z_i,\varepsilon_i] = \mathbb E_n\bigl[\varepsilon_i\,f_{B_i}\bigl((p + \zeta\varepsilon_i)\,q_\ast\bigr)\bigr],$$
--   with $B_i \sim \beta$ and $\varepsilon_i = \pm1$ with probability $1/2$ each. Then there is a constant $C > 0$ such that for every $n \ge 1$ and every $\zeta \in (0,p)$,
--   $$\Bigl|\frac1\zeta\,\mathrm{Cov}_n[Z_i,\varepsilon_i] - \Delta^{(n)}(p)\Bigr| \le \zeta\,C. \quad (A.9)$$
--
--   The covariance between a supplier's participation and its own payment perturbation thus estimates the marginal response at the unperturbed equilibrium with bias $O(\zeta)$, uniformly in the market size.
--
--   **Formalization Note** The covariance is written as the paper's own closed form $\mathbb E_n[\varepsilon_i f_{B_i}((p+\zeta\varepsilon_i)q_\ast)]$, printed on p. 38 right after (A.9); it equals the covariance of $Z_i$ and $\varepsilon_i$ because $\mathbb E\varepsilon_i = 0$ and $\mathbb P(Z_i = 1 \mid B_i, \varepsilon_i) = f_{B_i}((p + \zeta\varepsilon_i)q_\ast)$. Here $\varepsilon_i = (P_i - p)/\zeta$ with $P_i \sim \pi_{p,\zeta}$. "For every $\zeta$ and $n$" is read as $\zeta \in (0,p)$ (Lemma 1's range; payments must stay positive) and $n \ge 1$. $C$ depends on $p$ but not on $n$ or $\zeta$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 38, proof of Theorem 6, display (A.9) and the identity for Cov_n below it

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem eq_A9 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ζ ∈ Set.Ioo (0 : ℝ) p,
      |(1 / ζ) * (∫ b, ∫ P, (P - p) / ζ *
            M.f b (P * M.q n (M.muN n (perturbLaw p ζ))) ∂(perturbLaw p ζ) ∂M.β) -
          M.DeltaN n p| ≤ ζ * C := by sorry

end EquilibriumExperiment.Gradient
