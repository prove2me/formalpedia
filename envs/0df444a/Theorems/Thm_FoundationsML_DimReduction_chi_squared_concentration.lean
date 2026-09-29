-- Prove2me | Theorems.Thm_FoundationsML_DimReduction_chi_squared_concentration
-- name    : FoundationsML.DimReduction.chi_squared_concentration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:28:40.796615+00:00
-- url     : https://prove2.me/theorems/f6c95e2d-549d-4f53-9b39-ad6de6e05fdf
-- title:
--   Lemma 15.2 — Chi-squared concentration (milestone)
-- statement:
--   **Statement (Lemma 15.2, p. 354, PDF p. 371).** Let $Q$ be a random variable following a
--   $\chi^2$ distribution with $k$ degrees of freedom. Then, for any $0<\epsilon<1/2$,
--   $$P[(1-\epsilon)k \le Q \le (1+\epsilon)k] \ge 1-2e^{-(\epsilon^2-\epsilon^3)k/4}.$$
--
--   This is a two-sided concentration bound for the $\chi^2$ distribution, proved via a
--   Chernoff/Markov argument on the moment-generating function; it is the purely
--   distributional fact that Lemma 15.3 specializes to the particular $\chi^2$ variable arising
--   from a Gaussian random projection.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 354, Lemma 15.2 (PDF p. 371)

import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsChiSquaredMGF

open MeasureTheory

namespace FoundationsML.DimReduction

/-- Lemma 15.2 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 354, PDF p. 371). Let `Q` be a random variable following a `χ²` distribution
with `k` degrees of freedom. Then, for any `0 < ε < 1/2`,
`P[(1−ε)k ≤ Q ≤ (1+ε)k] ≥ 1 − 2exp(−(ε²−ε³)k/4)`. -/
theorem chi_squared_concentration {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : IsChiSquaredMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by sorry

end FoundationsML.DimReduction
