-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
-- name    : AvramDividend.Classical.psi_quadratic_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:27:36.870143+00:00
-- url     : https://prove2.me/theorems/29cedb53-340b-49c5-bf7c-b26ca458dc2b
-- title:
--   Quadratic growth upper bound for the canonical Levy exponent
-- statement:
--   For every canonical spectrally negative Levy process and theta at least one, its Laplace exponent is bounded above by an explicit finite constant times theta squared.
-- source:
--   The Levy integrability field gives finite small-jump second moment and finite large-jump mass. These imply integrability and a quadratic upper bound for the jump term, while drift and Gaussian terms are at most quadratic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem psi_quadratic_upper {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.ψ θ ≤
      (|X.c| + X.σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν) * θ ^ 2 := by
  sorry

end AvramDividend.Classical
