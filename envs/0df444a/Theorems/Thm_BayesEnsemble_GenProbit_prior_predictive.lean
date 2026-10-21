-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_prior_predictive
-- name    : BayesEnsemble.GenProbit.prior_predictive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:30.737918+00:00
-- url     : https://prove2.me/theorems/7f68bb53-ea86-464e-8c49-6c2277e6a788
-- title:
--   Proof of Proposition 4, p. 29 — prior-predictive probability
-- statement:
--   Under the jointly normal information-state law and the generalized linear event model, the event's prior-predictive probability is
--
--   $$
--   p_0=P(y=1)=F_{z_0+\sqrt{v_0}x_0}(m_0),\qquad
--   m_0=\alpha_0+\sum_i\alpha_i\mu_i,\quad
--   v_0=\sum_{i,j}\alpha_i\alpha_j\sigma_{ij}.
--   $$
--
--   The proof further concludes that $F^{-1}_{z_0+\sqrt{v_0}x_0}(p_0)=m_0$. This supplies the prior term of the ensemble in Proposition 4. **Formalization Note** $p_0$ is the measure of the event, and its displayed cdf expression is a conclusion. The event and the information-state map are measurable.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 29, proof of Proposition 4, “Finally, P(y = 1)”

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- The prior-predictive formula at the end of the proof of Proposition 4, p. 29. -/
theorem prior_predictive {k : ℕ} (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i)) :
    μ.real Y = G P (v0 P) (m0 P) ∧
    Ginv P (v0 P) (μ.real Y) = m0 P := by sorry

end BayesEnsemble.GenProbit
