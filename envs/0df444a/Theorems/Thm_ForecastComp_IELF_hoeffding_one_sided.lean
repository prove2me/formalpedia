-- Prove2me | Theorems.Thm_ForecastComp_IELF_hoeffding_one_sided
-- name    : ForecastComp.IELF.hoeffding_one_sided
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:49.746102+00:00
-- url     : https://prove2.me/theorems/c537977c-1d89-4602-8e4f-b20417305bca
-- title:
--   Theorem (Hoeffding's inequality), Appendix M, p. 35 — one-sided bounds e^{−2t²/m}
-- statement:
--   Let $X_1,\dots,X_m$ be independent real random variables on a probability space, each with values in $[0,1]$ almost surely, and let $S_m=X_1+\dots+X_m$. Then for every $t\ge0$,
--   $$\Pr\big(S_m-\mathbb E[S_m]\ge t\big)\le e^{-2t^2/m}\qquad\text{and}\qquad\Pr\big(\mathbb E[S_m]-S_m\ge t\big)\le e^{-2t^2/m}.$$
--
--   This is the one-sided form of Hoeffding's inequality (Hoeffding 1963) used in the proof of Theorem 7 to bound the deviation of the number of events a forecaster wins.
--
--   **Formalization Note** $t\ge0$ is added (the bound is false for $t<0$); at $m=0$ the exponent is read as $0$ and the bound $1$ holds trivially. The variables are measurable and mutually independent (`iIndepFun`).
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 35, Theorem (Hoeffding's inequality), Appendix M

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

open MeasureTheory ProbabilityTheory

/-- Hoeffding's inequality as stated in Appendix M, p. 35: for independent random variables
`X_1, …, X_m` with values in `[0,1]` and `S_m = X_1 + … + X_m`, both one-sided deviations of
`S_m` from its mean by at least `t ≥ 0` have probability at most `e^{−2t²/m}`. -/
theorem hoeffding_one_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, X k ω ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ k, X k ω) - ∫ ω', (∑ k, X k ω') ∂μ} ≤
        Real.exp (-2 * t ^ 2 / (m:ℝ)) ∧
    μ.real {ω | t ≤ (∫ ω', (∑ k, X k ω') ∂μ) - ∑ k, X k ω} ≤
        Real.exp (-2 * t ^ 2 / (m:ℝ)) := by sorry

end ForecastComp.IELF
