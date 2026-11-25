-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_objective_max_likelihood
-- name    : Arxiv2405_15536.kappa_objective_max_likelihood
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:22:17.295549+00:00
-- url     : https://prove2.me/theorems/94e8a019-58dd-4e1d-a1c7-167ca5e3d937
-- title:
--   Eqs. (11)-(12): the $\kappa$-objective is the negative $\kappa$-log-likelihood (as proved, sampled form)
-- statement:
--   Let $|\kappa|<2/3$, let $M$ be a set of models, and let $(\varepsilon_i(m))_{i\in I}$ be the errors of model $m$ at a finite set $I$ of $N=|I|$ samples (each sample is a source, a receiver and a time sample). Let $\mathcal L_\kappa(m)=\prod_{i\in I}p_\kappa(\varepsilon_i(m))$ be the κ-likelihood of eq. (11), and let
--
--   $$\phi_\kappa(m)=-\sum_{i\in I}\ln\big[\exp_\kappa\big(-\beta_\kappa\varepsilon_i(m)^2\big)\big]$$
--
--   be the sampled κ-objective. Then for every model $m$
--
--   $$-\ln\mathcal L_\kappa(m)=N\ln Z_\kappa+\phi_\kappa(m),$$
--
--   and $m$ minimises $\phi_\kappa$ over $M$ if and only if $m$ maximises $\mathcal L_\kappa$ over $M$.
--
--   This is the maximum-likelihood derivation of the κ-objective function (12).
--
--   **Formalization Note** The paper writes the likelihood as a product over $N$ samples and the objective as a time integral, and drops the constant $N\ln Z_\kappa$. The statement keeps the objective as the sum over the same samples; replacing the sum by a Riemann sum with a positive time step does not change the minimisers. The errors are arbitrary functions of the model: the derivation does not use the wave equation.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c003; Sec. 2.2, eqs. (11)-(12), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_objective_max_likelihood {M I : Type*} [Fintype I] (κ : ℝ) (hκ : |κ| < 2 / 3)
    (ε : M → I → ℝ) :
    (∀ m : M, -Real.log (kappaLikelihood κ (ε m)) =
      (Fintype.card I : ℝ) * Real.log (zKappa κ) + ∑ i, lossKappa κ (ε m i)) ∧
    (∀ m : M, (∀ m' : M, ∑ i, lossKappa κ (ε m i) ≤ ∑ i, lossKappa κ (ε m' i)) ↔
      (∀ m' : M, kappaLikelihood κ (ε m') ≤ kappaLikelihood κ (ε m))) := by sorry

end Arxiv2405_15536
