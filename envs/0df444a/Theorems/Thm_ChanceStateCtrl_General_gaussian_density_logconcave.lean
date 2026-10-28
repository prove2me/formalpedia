-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_gaussian_density_logconcave
-- name    : ChanceStateCtrl.General.gaussian_density_logconcave
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-25T01:00:26.234517+00:00
-- url     : https://prove2.me/theorems/d829a8ef-8d65-4113-8f3e-bd8dad2e7412
-- title:
--   p. 7 (proof of Lemma 2.5) — the nondegenerate Gaussian law N(0, Σ) has a log-concave Lebesgue density
-- statement:
--   Let $\Sigma$ be a symmetric positive definite $m\times m$ real matrix and let $\mathcal N(0,\Sigma)$ be the centered Gaussian distribution on $\mathbb R^m$ with covariance $\Sigma$ (Mathlib's `multivariateGaussian 0 Sigma`). Then $\mathcal N(0,\Sigma)$ is absolutely continuous with respect to Lebesgue measure, with a nonnegative measurable density $f_\xi$ that is **log-concave**:
--   $$
--   f_\xi(z)^t\,f_\xi(w)^{1-t}\le f_\xi\big(tz+(1-t)w\big)\qquad\text{for all } z,w\in\mathbb R^m,\ t\in[0,1].
--   $$
--   Explicitly one may take $f_\xi(z)=(2\pi)^{-m/2}(\det\Sigma)^{-1/2}\exp\!\big(-\tfrac12 z^\top\Sigma^{-1}z\big)$, whose logarithm is a concave quadratic.
--
--   This is the fact used on p. 7 of the source ("the density of our Gaussian random vector $\xi$ is log-concave") to apply Prékopa's theorem (log-concavity of the probability function $\varphi$) in the proof of Lemma 2.5.
--
--   **Formalization note.** The density is stated existentially, in exactly the form required by the hypotheses `hdens_nonneg`, `hdens_meas`, `hlaw`, `hdens_logconcave` of `ChanceStateCtrl.General.prekopa_logconcave`; the power $x^t$ is the real power `Real.rpow`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 7, proof of Lemma 2.5 ("the density of our Gaussian random vector ξ is log-concave")

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ChanceStateCtrl.General

theorem gaussian_density_logconcave {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hS : Sigma.PosDef) :
    ∃ dens : EuclideanSpace ℝ (Fin m) → ℝ, (∀ z, 0 ≤ dens z) ∧ Measurable dens ∧
      multivariateGaussian 0 Sigma = volume.withDensity (fun z => ENNReal.ofReal (dens z)) ∧
      ∀ z w : EuclideanSpace ℝ (Fin m), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dens z ^ t * dens w ^ (1 - t) ≤ dens (t • z + (1 - t) • w) := by sorry

end ChanceStateCtrl.General
