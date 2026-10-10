-- Prove2me | Theorems.Thm_BenfordLaw_benford_of_scale_invariant
-- name    : BenfordLaw.benford_of_scale_invariant
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:39.995627+00:00
-- url     : https://prove2.me/theorems/664d936b-30ad-449b-b85b-3ecd6c564568
-- title:
--   A scale-invariant first-digit distribution is Benford
-- statement:
--   Let $X$ be a random variable on a probability space with $X > 0$ almost surely. Suppose the distribution of its first decimal digit does not depend on the unit of measurement, i.e. for every $c > 0$ and every digit $d$,
--   $$\mathbb P\big(D_{10}(cX) = d\big) = \mathbb P\big(D_{10}(X)=d\big).$$
--   Then the first digit follows Benford's law: for $d\in\{1,\dots,9\}$,
--   $$\mathbb P\big(D_{10}(X) = d\big) = \log_{10}\!\left(1+\frac1d\right).$$
--
--   This turns the informal "units do not matter" argument of the source into a theorem.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Invariance" ("When the distribution of the first digits of a data set is scale-invariant (independent of the units that the data are expressed in), it is always given by Benford's law", refs. Pinkham 1961, https://doi.org/10.1214/aoms/1177704862).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem benford_of_scale_invariant {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : Measurable X) (hXpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hinv : ∀ c : ℝ, 0 < c → ∀ d : ℕ,
      P {ω | leadingDigit 10 (c * X ω) = d} = P {ω | leadingDigit 10 (X ω) = d})
    (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    (P {ω | leadingDigit 10 (X ω) = d}).toReal = benfordProb 10 d := by sorry

end BenfordLaw
