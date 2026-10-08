-- Prove2me | Theorems.Thm_CappeKLUCB_ExpFam_lemma_1
-- name    : CappeKLUCB.ExpFam.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:03.92372+00:00
-- url     : https://prove2.me/theorems/4d6dc7c7-ee0a-45f5-97fb-298861384c0c
-- title:
--   Lemma 1, p. 17 — 𝓛_ν(λ) ≤ 1 − μ + μ exp(λ) ≤ exp(λμ + 2λ²) for ν on [0, 1]
-- statement:
--   Let $\nu$ be a probability distribution on $[0,1]$ and let $\mu = \mathrm E(\nu) = \int x\,d\nu(x)$ be its expectation. Then for every $\lambda\in\mathbb R$,
--   $$\mathcal L_\nu(\lambda) = \int_{[0,1]} e^{\lambda x}\,d\nu(x) \le 1-\mu+\mu\exp(\lambda) \le \exp(\lambda\mu + 2\lambda^2).$$
--
--   The moment-generating function of any distribution on $[0,1]$ is dominated by that of the Bernoulli distribution with the same mean, which is in turn dominated by a Gaussian moment-generating function. This is why the Bernoulli divergence $d_{\mathrm{BER}}$ and the quadratic divergence $d_{\mathrm{QUAD}}$ are admissible in kl-UCB for arbitrary bounded rewards (Corollaries 1 and 2).
--
--   **Formalization Note** "$\nu\in\mathfrak M_1([0,1])$" is a probability measure on $\mathbb R$ giving zero mass to the complement of $[0,1]$. The constant $2\lambda^2$ is the printed one (the accompanying text, "variance $1/4$", corresponds to the sharper $\lambda^2/8$); the printed form is formalized.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 17, Lemma 1

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

namespace CappeKLUCB.ExpFam

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
  OptimalBAI.OptProportions

/-- Lemma 1, Cappé et al., arXiv:1210.1136v4, p. 17. -/
theorem lemma_1 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (l : ℝ) :
    ∫ x, Real.exp (l * x) ∂ν ≤ 1 - (∫ x, x ∂ν) + (∫ x, x ∂ν) * Real.exp l ∧
      1 - (∫ x, x ∂ν) + (∫ x, x ∂ν) * Real.exp l ≤
        Real.exp (l * (∫ x, x ∂ν) + 2 * l ^ 2) := by sorry

end CappeKLUCB.ExpFam
