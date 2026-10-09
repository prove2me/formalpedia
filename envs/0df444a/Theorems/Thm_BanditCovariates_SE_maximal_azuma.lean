-- Prove2me | Theorems.Thm_BanditCovariates_SE_maximal_azuma
-- name    : BanditCovariates.SE.maximal_azuma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:31.402326+00:00
-- url     : https://prove2.me/theorems/a55124e7-ae33-4920-bf36-11fd39f8de46
-- title:
--   Appendix p. 28 — maximal Hoeffding–Azuma inequality
-- statement:
--   Let $(Z_s)$ be an adapted martingale difference sequence with every term in a nondegenerate interval $[a,b]$, where $a<b$, almost surely. For $\eta>0$ and integer $t\ge1$, the chance that some partial sum through time $t$ reaches $\eta$ satisfies
--
--   $$P\!\left\{\exists s\in\{1,\ldots,t\}:\sum_{r=1}^{s}Z_r\ge\eta\right\}\le\exp\!\left(-\frac{2\eta^2}{t(b-a)^2}\right).$$
--
--   This maximal concentration bound is the input to the appendix's time-uniform estimate. The positive interval width makes the exponent well defined.
--
--   **Formalization Note** The first difference is explicitly centered, and conditioning is against an adapted filtration. The page leaves $a<b$ implicit; at $a=b$ its displayed quotient has a zero denominator.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 28, display in the proof of Lemma A.1 (maximal Hoeffding–Azuma)

import Mathlib
import Definitions.Def_BanditCovariates_SE_MartingaleDifference

namespace BanditCovariates.SE

open MeasureTheory ProbabilityTheory

/-- Appendix p. 28: the maximal Hoeffding–Azuma display recalled in the proof of Lemma A.1. -/
theorem maximal_azuma {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ)
    (hZ : MartingaleDifference P ℱ Z) (a b : ℝ) (hab : a < b)
    (hbound : ∀ n, ∀ᵐ ω ∂P, a ≤ Z n ω ∧ Z n ω ≤ b)
    (η : ℝ) (hη : 0 < η) (t : ℕ) (ht : 1 ≤ t) :
    P.real {ω | ∃ s ∈ Finset.Icc 1 t,
      η ≤ ∑ r ∈ Finset.range s, Z r ω} ≤
      Real.exp (-2 * η ^ 2 / ((t : ℝ) * (b - a) ^ 2)) := by sorry

end BanditCovariates.SE
