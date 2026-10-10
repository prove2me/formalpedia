-- Prove2me | Theorems.Thm_BenfordLaw_benford_of_uniform_log_mantissa
-- name    : BenfordLaw.benford_of_uniform_log_mantissa
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:31.819989+00:00
-- url     : https://prove2.me/theorems/cbd23db5-aa57-4156-851e-d2f069da59d3
-- title:
--   Uniform $\{\log_b X\}$ implies the first-digit law
-- statement:
--   Let $b\ge2$ and let $X$ be a random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ such that $X > 0$ almost surely and the fractional part $\{\log_b X\}$ is uniformly distributed on $[0,1)$. Then for every digit $d\in\{1,\dots,b-1\}$,
--   $$\mathbb P\big(D_b(X) = d\big) = \log_b\!\left(1+\frac1d\right).$$
--
--   This is the derivation of Benford's law from its strong form stated in the source.
--
--   **Formalization Note.** The hypothesis is `HasUniformLogMantissa b P X`; it includes measurability of $X$ and forces $\mathbb P$ to be a probability measure. The probability is stated as `(P {ω | leadingDigit b (X ω) = d}).toReal`.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Definition" ("this is the distribution expected if the logarithms of the numbers ... are uniformly and randomly distributed"; "Benford's law is sometimes stated in a stronger form ...").

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem benford_of_uniform_log_mantissa {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (hb : 2 ≤ b) (P : MeasureTheory.Measure Ω) (X : Ω → ℝ)
    (hX : HasUniformLogMantissa b P X) (d : ℕ) (hd1 : 1 ≤ d) (hdb : d < b) :
    (P {ω | leadingDigit b (X ω) = d}).toReal = benfordProb b d := by sorry

end BenfordLaw
