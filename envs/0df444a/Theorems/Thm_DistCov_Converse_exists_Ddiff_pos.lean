-- Prove2me | Theorems.Thm_DistCov_Converse_exists_Ddiff_pos
-- name    : DistCov.Converse.exists_Ddiff_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:31.444033+00:00
-- url     : https://prove2.me/theorems/54ab6f72-4476-403b-86b0-acb74dbe3399
-- title:
--   Proof of Proposition 3.15, p. 17 — off negative type there are µ₁ ≠ µ₂ with finite first moments and D(µ₁ − µ₂) > 0
-- statement:
--   Let $\mathcal X$ be a separable metric space that is **not** of negative type. Then there exist Borel probability measures $\mu_1\neq\mu_2$ on $\mathcal X$, both with finite first moments, such that
--   $$D(\mu_1-\mu_2)>0.$$
--
--   This is the case "$>0$ applies if $\mathcal X$ does not have negative type" of the second sentence of the proof of Proposition 3.15; the paper leaves the passage from a violation of (3.1) to such a pair implicit.
--
--   **Formalization Note.** Separability is the standing assumption of Errata (i). Negative type is the finite-sum condition (3.1), not an embedding property.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, proof of Proposition 3.15, second sentence; (3.1), p. 9

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem exists_Ddiff_pos
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (hX : ¬ DistCov.Indep.NegType X) :
    ∃ μ₁ μ₂ : Measure X, IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
      DistCov.Indep.FiniteFirstMoment μ₁ ∧ DistCov.Indep.FiniteFirstMoment μ₂ ∧ μ₁ ≠ μ₂ ∧ 0 < DistCov.Indep.Ddiff μ₁ μ₂ := by sorry

end DistCov.Converse
