-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_6
-- name    : DeltaSLearning.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:58.598987+00:00
-- url     : https://prove2.me/theorems/2ada0ae4-0c3c-462e-9f6b-37e8f6c30748
-- title:
--   Lemma 6 — exponential tails give sub-exponential parameters $(2\sqrt{c_1}/c_2,\,2/c_2)$
-- statement:
--   Let $X$ be a centered random variable, $\mathbb E[X]=0$, and let $c_1,c_2>0$ be such that
--   $$P[|X|\ge t]\le c_1e^{-c_2t}\qquad\text{for all }t>0 .$$
--   Then $X$ is sub-exponential with parameters $(2\sqrt{c_1}/c_2,\ 2/c_2)$ (Definition 5): $\mathbb E[e^{\lambda X}]\le e^{\nu^2\lambda^2/2}$ for all $|\lambda|<c_2/2$, with $\nu=2\sqrt{c_1}/c_2$.
--
--   The paper notes this lemma is not in the literature; it turns the tail bounds of the cycle quantities into the sub-exponential parameters of Lemma 3.
--
--   Differences from the source:
--   - generalization: P[|X| ≥ t] ≤ c₁ exp(−c₂ t), range of t not stated → the tail bound is assumed only for t > 0; reason: a bound for all t ≥ 0 implies the bound for t > 0, so the Lean statement specializes to every reading; t > 0 is Theorem 7(b)'s form (p.43)
--   - reading: constants c_1, c_2, sign not stated → c₁ > 0, c₂ > 0; reason: √c₁ and 1/c₂ in the conclusion; Theorem 7(b) states c1, c2 > 0
--   - encoding: a centered random variable → X measurable with ∫ X dP = 0 on a probability space; reason: the tail bound makes X integrable, so the mean is the genuine one
--   - encoding: sub-exponential (Definition 5) → the published HighDimStat.TailBounds.IsSubExponential, which also requires integrability of X and of the exponential moments; reason: Definition 5's E[X] and E[e^{λ(X−µ)}] presuppose them
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 6, p.44; Definition 5, p.43

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Lemma 6.** A centered random variable `X` with `P[|X| ≥ t] ≤ c₁ exp(-c₂ t)` for all
`t > 0` (`c₁, c₂ > 0`) is sub-exponential with parameters `(2√c₁/c₂, 2/c₂)` (Definition 5).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 6, p.44; Definition 5, p.43.

**Formalization Note** The page gives no range for `t`; we require the tail bound for `t > 0`
only, the form of Theorem 7(b) (p.43), which is a weaker hypothesis than `t ≥ 0`. "Centered" is
`E[X] = 0`; the tail bound makes `X` integrable. Definition 5 is the published
`HighDimStat.TailBounds.IsSubExponential`. -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hmean : ∫ ω, X ω ∂P = 0) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (c₁ * Real.exp (-(c₂ * t)))) :
    HighDimStat.TailBounds.IsSubExponential X P (2 * Real.sqrt c₁ / c₂) (2 / c₂) := by sorry

end DeltaSLearning
