-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_proposition_10
-- name    : EquilibriumExperiment.Gradient.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:36.698106+00:00
-- url     : https://prove2.me/theorems/5b41e2db-6149-4a75-8678-b91826ca8982
-- title:
--   Proposition 10, p. 36 — d/dμ q^{(n)}(μ) ≤ 0 and converges to −ω′(d_a/μ) d_a/μ²
-- statement:
--   Under the standing assumptions, fix $\mu \in (0,1]$. Then:
--   1. for every $n$, the derivative of $q^{(n)}(\mu) = \mathbb E[\Omega(D,X)]$, $X \sim \mathrm{Binomial}(n,\mu)$, is non-positive: $\frac{d}{d\mu}q^{(n)}(\mu) \le 0$;
--   2. $\frac{d}{d\mu}\,\omega(d/\mu) = -\omega'(d/\mu)\,\dfrac{d}{\mu^2}$;
--   3. if moreover $\mu < 1$,
--   $$\lim_{n\to\infty}\frac{d}{d\mu}q^{(n)}(\mu) = \frac{d}{d\mu}\,\omega(d/\mu) = -\omega'(d/\mu)\,\frac{d}{\mu^2}. \quad (A.3)$$
--
--   The proposition says that the pre-limit matching rate per supplier decreases in the supply parameter and that its sensitivity converges to that of the mean-field matching rate; it is the input to the limit (3.16) and to the interference correction in Lemma 4.
--
--   **Formalization Note** The paper fixes $\mu > 0$; here $\mu \le 1$ because $\mu$ is a binomial parameter. The limit is stated for $\mu < 1$: at $\mu = 1$ the derivative equals $n\,\mathbb E[\Omega(D,n) - \Omega(D,n-1)]$, whose error part $n(l(D,n) - l(D,n-1))$ is not controlled by the $o(1/\sqrt t + 1/\sqrt d)$ assumption on $l$. $q^{(n)}$ is the finite binomial sum, a polynomial in $\mu$, so its derivative is an honest derivative. $\omega'$ is Lean's `deriv`; $\omega$ is smooth on $(0,\infty)$ and $d/\mu > 0$. The proof in Appendix B.3 goes through Lemma 15, which is misprinted (its identity omits a factor $\eta'(\theta)$); this statement does not depend on it.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 36, Proposition 10, eq. (A.3); proof in Appendix B.3, pp. 43–46

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem proposition_10 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∀ n : ℕ, deriv (M.q n) μ ≤ 0) ∧
    HasDerivAt (fun m : ℝ => M.ω (M.d / m)) (-deriv M.ω (M.d / μ) * (M.d / μ ^ 2)) μ ∧
    (μ < 1 → Tendsto (fun n : ℕ => deriv (M.q n) μ) atTop
      (𝓝 (-deriv M.ω (M.d / μ) * (M.d / μ ^ 2)))) := by sorry

end EquilibriumExperiment.Gradient
