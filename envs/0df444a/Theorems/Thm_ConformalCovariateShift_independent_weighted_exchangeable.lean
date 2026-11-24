-- Prove2me | Theorems.Thm_ConformalCovariateShift_independent_weighted_exchangeable
-- name    : ConformalCovariateShift.independent_weighted_exchangeable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:23:02.363164+00:00
-- url     : https://prove2.me/theorems/adf9b766-cac2-4059-b516-7da544cf4f1a
-- title:
--   Lemma 2: independent draws are weighted exchangeable
-- statement:
--   Let $n\ge1$ and let $Z_1,\dots,Z_n$ be independent random variables with values in a measurable space $E$, $Z_i\sim P_i$, where each $P_i$ is absolutely continuous with respect to $P_1$. Then $Z_1,\dots,Z_n$ are weighted exchangeable with weight functions
--
--   $$w_1\equiv1,\qquad w_i=\frac{dP_i}{dP_1},\quad i\ge2.$$
--
--   This shows that the covariate-shift model, and more generally any independent sample whose laws are dominated by the first one, falls under the weighted theory.
--
--   **Formalization Note** Indices run over $0,\dots,n$ in Lean, index $0$ playing the role of the paper's index $1$. The Radon–Nikodym derivative is Mathlib's version `rnDeriv`, which takes values in $[0,\infty]$ and is finite almost everywhere; it is converted to a real number.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 3.2, Lemma 2, p. 12

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem independent_weighted_exchangeable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P] {n : ℕ} (Z : Fin (n + 1) → Omega → E)
    (Pm : Fin (n + 1) → Measure E) (hZm : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, Measure.map (Z i) P = Pm i) (hac : ∀ i, Pm i ≪ Pm 0) :
    IsWeightedExchangeable P Z
      (fun i z => if i = 0 then 1 else ((Pm i).rnDeriv (Pm 0) z).toReal) := by sorry

end ConformalCovariateShift
