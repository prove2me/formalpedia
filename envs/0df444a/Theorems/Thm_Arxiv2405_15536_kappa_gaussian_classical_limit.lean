-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_gaussian_classical_limit
-- name    : Arxiv2405_15536.kappa_gaussian_classical_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:11:24.001449+00:00
-- url     : https://prove2.me/theorems/898bd0a5-0d60-4d3c-b730-5c453803f430
-- title:
--   Eq. (10): the Gaussian is the $\kappa\to0$ limit of the $\kappa$-Gaussian
-- statement:
--   Let $\exp_\kappa$, $\beta_\kappa$, $Z_\kappa$ and $p_\kappa$ be given by eqs. (6)-(9). As $\kappa\to0$ ($\kappa\neq0$),
--
--   $$Z_\kappa\to\sqrt{2\pi},\qquad \beta_\kappa\to\tfrac12,\qquad \exp_\kappa(y)\to e^{y}\ \text{ for every }y\in\mathbb{R},$$
--
--   and consequently, for every $\varepsilon\in\mathbb{R}$,
--
--   $$p_\kappa(\varepsilon)\to p_0(\varepsilon)=\frac{1}{\sqrt{2\pi}}e^{-\varepsilon^2/2}.$$
--
--   Thus the standard Gaussian (eq. 10) is the classical limit of the κ-Gaussian family.
--
--   **Formalization Note** The Gaussian density is Mathlib's `gaussianPDFReal 0 1`. The limits are two-sided limits over the punctured neighbourhood of $0$, so they concern the printed formulas for $\kappa\neq0$ and not the values assigned at $\kappa=0$.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c001; Sec. 2.2, eqs. (6)-(10) and the text after eq. (10), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_gaussian_classical_limit :
    Tendsto zKappa (𝓝[≠] 0) (𝓝 (Real.sqrt (2 * Real.pi))) ∧
    Tendsto betaKappa (𝓝[≠] 0) (𝓝 (1 / 2)) ∧
    (∀ y : ℝ, Tendsto (fun κ => expKappa κ y) (𝓝[≠] 0) (𝓝 (Real.exp y))) ∧
    (∀ ε : ℝ, Tendsto (fun κ => kappaGaussian κ ε) (𝓝[≠] 0)
      (𝓝 (ProbabilityTheory.gaussianPDFReal 0 1 ε))) := by sorry

end Arxiv2405_15536
