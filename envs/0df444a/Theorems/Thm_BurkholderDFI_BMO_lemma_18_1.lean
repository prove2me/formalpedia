-- Prove2me | Theorems.Thm_BurkholderDFI_BMO_lemma_18_1
-- name    : BurkholderDFI.BMO.lemma_18_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:53.332871+00:00
-- url     : https://prove2.me/theorems/47f64ae0-b0ec-4985-b4ee-797b5d87a631
-- title:
--   Lemma 18.1 — tail integral control gives exponential integrability
-- statement:
--   Let $g$ be a nonnegative measurable function on a probability space, and let $\alpha>0$. Suppose that for every $a>0$,
--
--   $$\int_a^\infty P(g>x)\,dx\le\alpha P(g>a).$$
--
--   Then $g$ is finite almost surely and, for every $0<t<\alpha^{-1}$,
--
--   $$\mathbf E[e^{tg}]\le\frac{1}{1-\alpha t}.$$
--
--   The lemma converts a distribution-tail inequality into an exponential moment bound and is reused for Theorem 19.1 with $g=S(f)^2$.
--
--   **Formalization Note** The function has values in $[0,\infty]$. Almost-sure finiteness is stated explicitly before converting its finite values to real numbers inside the exponential; otherwise an infinite value would be converted to zero. The expectation is a nonnegative integral, so non-integrability does not produce a default zero.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 18.1, p. 36, https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Lemma 18.1, p. 36: a tail integral bound implies an exponential moment bound. -/
theorem lemma_18_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    (∀ᵐ ω ∂P, g ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < α⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - α * t)) := by sorry

end BurkholderDFI.BMO
