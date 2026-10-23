-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_lemma_4
-- name    : EquilibriumExperiment.Gradient.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:32.137388+00:00
-- url     : https://prove2.me/theorems/8032eedb-6ce9-4905-bf19-c719904fa737
-- title:
--   Lemma 4, p. 19 — implicit derivative (3.18) of the equilibrium supply and its mean-field limits (3.19)–(3.20)
-- statement:
--   Under the standing assumptions, fix a payment $p > 0$. Then:
--   1. (3.18) for every $n \ge 1$, $p \mapsto \mu^{(n)}(p)$ is differentiable at $p$ with
--   $$\frac{d}{dp}\mu^{(n)}(p) = \frac{\Delta^{(n)}(p)}{1 - p\,\Delta^{(n)}(p)\,q^{(n)\prime}\bigl(\mu^{(n)}(p)\bigr)\big/q^{(n)}\bigl(\mu^{(n)}(p)\bigr)};$$
--   2. if moreover $\mathbb E[f_B(p\,\bar\omega)] > 0$, then (3.19) $\lim_{n\to\infty}\Delta^{(n)}(p) = \Delta(p) = \omega(d/\mu(p))\,\mathbb E[f_B'(p\,\omega(d/\mu(p)))]$, and (3.20) $p \mapsto \mu(p)$ is differentiable at $p$ with
--   $$\lim_{n\to\infty}\frac{d}{dp}\mu^{(n)}(p) = \mu'(p) = \Delta(p)\Big/\Bigl(1 + \frac{p\,d\,\Delta(p)\,\omega'(d/\mu(p))}{\mu(p)^2\,\omega(d/\mu(p))}\Bigr).$$
--
--   The lemma separates the supply response to a price change into the marginal response $\Delta$, which local experiments can estimate, and an interference correction determined by the matching function; it is what turns an estimate of $\Delta$ into an estimate of $\mu'(p)$.
--
--   **Formalization Note** The paper's $p \in \mathbb R_+$ is taken as $p > 0$ (Definition 9 fixes $p > 0$). The positivity condition $\mathbb E[f_B(p\bar\omega)] > 0$ makes $\mu(p)$ exist (see Lemma 2). "$= \mu_a'(p)$" in (3.20) is formalized as differentiability of $\mu(\cdot)$ at $p$ with that derivative. When $q^{(n)}(\mu^{(n)}(p)) = 0$ or $\omega(d/\mu(p)) = 0$, the formulas take Lean's value $x/0 = 0$ inside the denominator, which gives $\Delta/1 = 0$; in those cases $\Delta = 0$ and the true derivative is $0$, so the statement remains the paper's.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 19, Lemma 4, eqs. (3.18)–(3.20); Definition 9, (3.17); proof in Appendix A.3, p. 37

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem lemma_4 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) :
    (∀ n : ℕ, 1 ≤ n →
      HasDerivAt (fun p' : ℝ => M.muN n (Measure.dirac p'))
        (M.DeltaN n p / (1 - p * M.DeltaN n p * deriv (M.q n) (M.muN n (Measure.dirac p)) /
          M.q n (M.muN n (Measure.dirac p)))) p) ∧
    (0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β →
      Tendsto (fun n : ℕ => M.DeltaN n p) atTop (𝓝 (M.DeltaLim p)) ∧
      Tendsto (fun n : ℕ => deriv (fun p' : ℝ => M.muN n (Measure.dirac p')) p) atTop
        (𝓝 (M.muLimDeriv p)) ∧
      HasDerivAt M.muLim (M.muLimDeriv p) p) := by sorry

end EquilibriumExperiment.Gradient
