-- Prove2me | Theorems.Thm_ConformalCovariateShift_quantile_lemma
-- name    : ConformalCovariateShift.quantile_lemma
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:22:09.833039+00:00
-- url     : https://prove2.me/theorems/e0bee71a-6366-4381-9d2e-dbf305b13e98
-- title:
--   Lemma 1: quantile lemma
-- statement:
--   Let $V_1,\dots,V_{n+1}$ be exchangeable real random variables on a probability space, $n\ge0$, and let $\beta\in(0,1)$. Then
--
--   $$\mathbb{P}\Big\{V_{n+1}\le\mathrm{Quantile}\big(\beta;V_{1:n}\cup\{\infty\}\big)\Big\}\ge\beta.$$
--
--   If moreover ties among $V_1,\dots,V_{n+1}$ occur with probability zero, that is $\mathbb{P}\{V_i=V_j\text{ for some }i\ne j\}=0$, then the same probability is at most $\beta+1/(n+1)$.
--
--   This is the quantile lemma on which conformal prediction rests.
--
--   **Formalization Note** Exchangeability includes measurability of each $V_i$. The probability of the event is written as the measure of the set of outcomes where it holds.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 1.1, Lemma 1, p. 2

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem quantile_lemma {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    {n : ℕ} (V : Fin (n + 1) → Omega → ℝ) (hV : IsExchangeable P V)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal β ≤ P {ω | (V (Fin.last n) ω : EReal) ≤ quantileWithInf β (fun i => V i ω)} ∧
    (P {ω | ∃ i j, i ≠ j ∧ V i ω = V j ω} = 0 →
      P {ω | (V (Fin.last n) ω : EReal) ≤ quantileWithInf β (fun i => V i ω)} ≤
        ENNReal.ofReal (β + 1 / ((n : ℝ) + 1))) := by sorry

end ConformalCovariateShift
