-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_report_formula
-- name    : BayesEnsemble.GenProbit.report_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:17.234581+00:00
-- url     : https://prove2.me/theorems/65ae0788-b62e-4a3d-a5d2-e48c2d246783
-- title:
--   Proof of Proposition 4, p. 29 — each expert report
-- statement:
--   Under the jointly normal information-state law and the generalized linear event model, expert $i$ reports the conditional event probability $p_i=P(y=1\mid x_i)$. Its closed form is
--
--   $$
--   p_i=F_{z_0+\sqrt{v_i}x_0}\!\left(m_0+\beta_i^{-1}\alpha_i(x_i-\mu_i)\right).
--   $$
--
--   This identifies an actual conditional probability with the formula appearing in Proposition 4. The equality holds almost surely because the conditional probability is a version. **Formalization Note** The report is defined by conditional expectation of the event indicator; its closed form is the conclusion, never a model hypothesis.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 29, proof of Proposition 4, “From the expressions above, we can rewrite expert i’s reported probability”

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- The report formula at the end of the chain on p. 29. -/
theorem report_formula {k : ℕ} (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i))
    (i : Fin k) :
    report μ x Y i =ᵐ[μ] fun ω =>
      G P (vi P i) (m0 P + (beta P i)⁻¹ * P.alpha i * (x ω i - P.mean i)) := by sorry

end BayesEnsemble.GenProbit
