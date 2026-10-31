-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2
-- name    : EquilibriumExperiment.Gradient.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:38.016767+00:00
-- url     : https://prove2.me/theorems/9468ea90-2c41-40d4-aebf-c90b4c9622b8
-- title:
--   Lemma 2 (3.13)–(3.14), p. 18 — μ^{(n)}(p) → μ_a(p), the unique root of the mean-field balance equation, and q^{(n)}(μ) → ω(d_a/μ)
-- statement:
--   Under the standing assumptions:
--   1. (3.13) for every payment $p > 0$ with $\mathbb E[f_B(p\,\bar\omega)] > 0$, where $\bar\omega = \sup_{x \ge 0}\omega(x)$, the mean-field balance equation
--   $$\mu = \mathbb E\bigl[f_B\bigl(p\,\omega(d/\mu)\bigr)\bigr]$$
--   has exactly one solution $\mu(p) \in (0,1]$, and the equilibrium supply converges to it:
--   $$\lim_{n\to\infty}\mu^{(n)}(p) = \mu(p);$$
--   2. (3.14) for every $\mu \in (0,1]$,
--   $$\lim_{n\to\infty} q^{(n)}(\mu) = \omega(d/\mu).$$
--
--   These are the mean-field limits of the equilibrium supply and of the matching rate; every later limit (Lemma 4, Proposition 12, Theorem 6) is taken around $\mu(p)$.
--
--   **Formalization Note** Only (3.13) and (3.14) of Lemma 2 are formalized. (3.15) concerns the pre-limit utility $u^{(n)}$, which is not modelled; its right-hand side is the definition of $u$. (3.16) is the limit of Proposition 10, formalized there. The hypothesis $\mathbb E[f_B(p\bar\omega)] > 0$ is exactly the condition under which a solution in $(0,1]$ exists (if it fails, the right-hand side vanishes for every $\mu$); it makes explicit the paper's presupposition that "the limit $\mu_a(p)$ is the only solution". The ranges $p > 0$ and $\mu \in (0,1]$ replace the paper's $p,\mu \in \mathbb R_+$: Lemma 1 requires $p > 0$, $\omega(d/\mu)$ is undefined at $\mu = 0$, and $\mu$ is a binomial parameter.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 18, Lemma 2, eqs. (3.13)–(3.14); proof in Appendix A.2, pp. 36–37

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem lemma_2 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing) :
    (∀ p : ℝ, 0 < p → 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β →
      (∃! μ : ℝ, μ ∈ Set.Ioc (0 : ℝ) 1 ∧ μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β) ∧
      Tendsto (fun n : ℕ => M.muN n (Measure.dirac p)) atTop (𝓝 (M.muLim p))) ∧
    (∀ μ : ℝ, μ ∈ Set.Ioc (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => M.q n μ) atTop (𝓝 (M.ω (M.d / μ)))) := by sorry

end EquilibriumExperiment.Gradient
