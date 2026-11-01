-- Prove2me | Theorems.Thm_EThetaPoula_Risk_pi_beta_moments
-- name    : EThetaPoula.Risk.pi_beta_moments
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:35.855971+00:00
-- url     : https://prove2.me/theorems/ff83a7de-4c9a-45ba-8d30-085144f8ab47
-- title:
--   §6.1, p.22 — $\pi_\beta$ has a finite $2p$-th moment for every $p$
-- statement:
--   Under Assumptions 1–4, for $\beta>0$ with $\int e^{-\beta u}<\infty$, $\pi_\beta$ is a probability measure and
--   $$
--   \int_{\mathbb R^d}|\theta|^{2p}\,\pi_\beta(d\theta)<\infty\qquad\text{for every }p\in\mathbb N.
--   $$
--
--   This makes $\int V_2\,d\pi_\beta$ and $c_{Z_\infty,4r+2}$ in the constants real numbers.
--
--   Differences from the source:
--   - generalization: a filtration $(\mathcal G_n)$ with $(X_n)$ adapted, and $\theta_0$, $\mathcal G_\infty$, $(\xi_n)$ independent → no filtration; $\theta_0$, $(X_n)_n$, $(\xi_n)_n$ mutually independent as three random objects; reason: independence with $\mathcal G_\infty$ implies this, because $\sigma(X_n:n)\subseteq\mathcal G_\infty$; the filtration plays no other role in the statement
--   - encoding: $u(\theta):=E[U(\theta,X)]$ → $E[U(\theta,X_0)]$; reason: $X_0$ has the law of $X$
--   - reading: $a$ is the smallest eigenvalue of $E[A(X_0)]$ and $b$ the largest eigenvalue of $E[B(X_0)]$, with $A,B$ not assumed symmetric → $a$, $b$ are the minimum and the maximum of the Rayleigh quotient on the unit sphere; reason: every use of the assumption is through the quadratic forms; the two agree on symmetric means, and a non-symmetric matrix can have a form below its smallest eigenvalue
--   - generalization: $\int e^{-\beta u}<\infty$ assumed for any $\beta>0$ → $\int e^{-\beta u}<\infty$ required for the fixed $\beta$ of the statement only; reason: a weaker hypothesis; the printed one implies it
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **`π_β` has finite moments**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22: under
Assumptions 1–4, `π_β` is a probability measure with a finite `2p`-th moment for every `p ∈ ℕ`.

**Formalization Note.** That `π_β` is a probability measure is the content of the normalization in (3);
it is stated because `gibbsMeasure` is a `withDensity`. -/
theorem pi_beta_moments {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (hS : S.Admissible) (hA : S.Assumptions C) (β : ℝ) (hβ : 0 < β)
    (hgibbs : Integrable fun θ : Eucl d => Real.exp (-β * S.u θ)) :
    IsProbabilityMeasure (S.piBeta β) ∧
    ∀ p : ℕ, Integrable (fun θ : Eucl d => ‖θ‖ ^ (2 * p)) (S.piBeta β) := by sorry

end EThetaPoula.Risk
