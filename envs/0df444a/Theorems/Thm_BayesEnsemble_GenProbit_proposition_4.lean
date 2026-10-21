-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_proposition_4
-- name    : BayesEnsemble.GenProbit.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:17.284592+00:00
-- url     : https://prove2.me/theorems/bdab74fd-08b6-4a05-a56b-34af3468e6eb
-- title:
--   Proposition 4, p. 14 — generalized probit ensemble
-- statement:
--   Let the experts' information states be jointly normal with mean $\mu$ and covariance $\Sigma$, and suppose the conditional event probability given the full state is $F_{z_0}(\alpha_0+\sum_i\alpha_i x_i)$. Let $p_i=P(y=1\mid x_i)$, $p_0=P(y=1)$, and $\hat p=P(y=1\mid p_1,\ldots,p_k)$. Then
--
--   $$
--   \hat p=F_{z_0}\!\left(\beta_0F^{-1}_{z_0+\sqrt{v_0}x_0}(p_0)
--   +\sum_i\beta_iF^{-1}_{z_0+\sqrt{v_i}x_0}(p_i)\right).
--   $$
--
--   The proposition also identifies $p_0=F_{z_0+\sqrt{v_0}x_0}(m_0)$ and $p_i=F_{z_0+\sqrt{v_i}x_0}(m_0+\beta_i^{-1}\alpha_i(x_i-\mu_i))$. Here $m_0=\alpha_0+\sum_i\alpha_i\mu_i$, $v_0=\sum_{i,j}\alpha_i\alpha_j\sigma_{ij}$, $v_i=\sum_{j,j'\ne i}\alpha_j\alpha_{j'}\sigma_{jj'}-(\sum_{j\ne i}\alpha_j\sigma_{ij})^2/\sigma_{ii}$, $\beta_i=\alpha_i\sqrt{\sigma_{ii}}/(\sum_j\alpha_j\sqrt{\sigma_{jj}}\rho_{ij})$, and $\beta_0=1-\sum_i\beta_i$.
--
--   This is the paper's Bayesian aggregation rule for correlated, normally distributed information states. **Formalization Note** The three identities hold almost surely where they concern conditional probabilities. The assumptions explicitly include $\alpha_i\ne0$, $\sigma_{ii}>0$, and $\sum_j\alpha_j\sigma_{ij}\ne0$; the law of $z_0$ is absolutely continuous and has full real support. The location-scale family is represented by its standard member with location zero and scale one.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 14, Proposition 4

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- Proposition 4, p. 14: the generalized probit ensemble is the Bayesian aggregate. -/
theorem proposition_4 {k : ℕ} (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) :
    μ.real Y = G P (v0 P) (m0 P) ∧
    (∀ i, report μ x Y i =ᵐ[μ] fun ω =>
      G P (vi P i) (m0 P + (beta P i)⁻¹ * P.alpha i * (x ω i - P.mean i))) ∧
    aggregate μ x Y =ᵐ[μ] fun ω =>
      ensemble P (μ.real Y) (fun i => report μ x Y i ω) := by sorry

end BayesEnsemble.GenProbit
