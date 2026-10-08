-- Prove2me | Theorems.Thm_BurkholderDFI_NonnegExp_lemma_18_1
-- name    : BurkholderDFI.NonnegExp.lemma_18_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:36.729704+00:00
-- url     : https://prove2.me/theorems/085cf0fc-be9f-4bd3-a7b8-4a3b622c0b64
-- title:
--   Lemma 18.1 — integrated tail control implies an exponential moment
-- statement:
--   Let $g$ be a nonnegative measurable function on a probability space and let $\alpha>0$. Suppose that for every $a>0$,
--
--   $$
--   \int_a^\infty P(g>x)\,dx\le\alpha P(g>a).
--   $$
--
--   Then $g$ is exponentially integrable and, for every $0<t<\alpha^{-1}$,
--
--   $$
--   E e^{tg}\le\frac{1}{1-\alpha t}.
--   $$
--
--   This tail-to-moment implication is independent of martingales and is reused for both Theorems 18.1 and 19.1.
--
--   **Formalization Note** The extended nonnegative value $g=\infty$ is permitted in the input type; the tail condition forces $g<\infty$ almost everywhere, stated as a separate conclusion. The exponential formula then converts finite values to real numbers, avoiding the default conversion of $\infty$ to zero.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Lemma 18.1, p. 36; https://doi.org/10.1214/aop/1176997023

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Lemma 18.1, p. 36: an integrated tail bound implies exponential integrability. -/
theorem lemma_18_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω} ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    (∀ᵐ ω ∂P, g ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < α⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P ≤ ENNReal.ofReal (1 / (1 - α * t)) := by sorry

end BurkholderDFI.NonnegExp
