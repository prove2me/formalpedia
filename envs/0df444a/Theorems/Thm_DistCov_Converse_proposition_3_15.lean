-- Prove2me | Theorems.Thm_DistCov_Converse_proposition_3_15
-- name    : DistCov.Converse.proposition_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:58.705763+00:00
-- url     : https://prove2.me/theorems/b5f1cb2a-0eef-4341-bdde-461c53093793
-- title:
--   Proposition 3.15 — without (strong) negative type, distance covariance fails to characterize independence
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces, and suppose $\mathcal Y$ has at least two points.
--
--   1. If $\mathcal X$ is not of negative type, there is a Borel probability measure $\theta$ on $\mathcal X\times\mathcal Y$ whose marginals have finite first moments and such that
--   $$\operatorname{dcov}(\theta)<0.$$
--   2. If $\mathcal X$ is not of strong negative type, there is a Borel probability measure $\theta$ on $\mathcal X\times\mathcal Y$ whose marginals have finite first moments and such that
--   $$\operatorname{dcov}(\theta)=0,$$
--   yet $\theta$ is not a product measure.
--
--   Theorem 3.11 of the paper says that on spaces of strong negative type, $\operatorname{dcov}(\theta)=0$ forces $\theta$ to be the product of its marginals, so that distance covariance characterizes independence. This proposition shows that the hypothesis on $\mathcal X$ cannot be dropped: without negative type distance covariance can be negative, and without strong negative type it can vanish on a dependent law.
--
--   **Formalization Note.** Separability of $\mathcal X$ and $\mathcal Y$ is the standing assumption of the author's Errata (i); it makes $d$ measurable for the product Borel $\sigma$-field. "For every metric space $\mathcal Y$ with at least two points" is rendered by taking $\mathcal Y$ as a universally quantified parameter, with the hypothesis that it has two distinct points; $\theta$ is chosen after $\mathcal Y$. "Not a product measure" means $\theta$ differs from the product of its own marginals. Part 2's hypothesis is the bare negation of strong negative type and so covers spaces of negative type as well as spaces that fail it.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, Proposition 3.15; Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem proposition_3_15
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (hY : ∃ y₁ y₂ : Y, y₁ ≠ y₂) :
    (¬ DistCov.Indep.NegType X → ∃ θ : Measure (X × Y), IsProbabilityMeasure θ ∧
        DistCov.Indep.FiniteFirstMoment (θ.map Prod.fst) ∧ DistCov.Indep.FiniteFirstMoment (θ.map Prod.snd) ∧ DistCov.Indep.dcov θ < 0) ∧
    (¬ DistCov.Indep.StrongNegType X → ∃ θ : Measure (X × Y), IsProbabilityMeasure θ ∧
        DistCov.Indep.FiniteFirstMoment (θ.map Prod.fst) ∧ DistCov.Indep.FiniteFirstMoment (θ.map Prod.snd) ∧
        DistCov.Indep.dcov θ = 0 ∧ ¬ DistCov.Indep.IsProduct θ) := by sorry

end DistCov.Converse
