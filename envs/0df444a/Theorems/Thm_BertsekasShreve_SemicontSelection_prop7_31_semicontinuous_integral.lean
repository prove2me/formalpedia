-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_prop7_31_semicontinuous_integral
-- name    : BertsekasShreve.SemicontSelection.prop7_31_semicontinuous_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:58.557192+00:00
-- url     : https://prove2.me/theorems/bb37965c-f0c9-45fd-9ee2-542c452e28e7
-- title:
--   Proposition 7.31 — integrating a semicontinuous function against a continuous kernel preserves semicontinuity
-- statement:
--   Let $X$ and $Y$ be separable metrizable spaces, let $q(dy\mid x)$ be a continuous stochastic kernel on $Y$ given $X$ (a continuous map from $X$ into the space $P(Y)$ of Borel probability measures with the weak topology), and let $f:X\times Y\to R^*$ be Borel-measurable. Define
--
--   $$\lambda(x)=\int f(x,y)\,q(dy\mid x)\qquad(x\in X),$$
--
--   the integral of the extended-real-valued function $y\mapsto f(x,y)$ in the sense $\int f^+-\int f^-$ with $\infty-\infty=\infty$.
--
--   1. If $f$ is lower semicontinuous and bounded below by a real number, then $\lambda$ is lower semicontinuous and bounded below by a real number.
--   2. If $f$ is upper semicontinuous and bounded above by a real number, then $\lambda$ is upper semicontinuous and bounded above by a real number.
--
--   This is the semicontinuity of the expectation step of the dynamic programming algorithm: under a continuous transition kernel, the expected cost-to-go inherits semicontinuity from the cost-to-go.
--
--   **Formalization Note** The integral is the published definition `DupacovaWets.Consistency.expect`, which is exactly Eq. (43) of Chapter 7 with the convention (42): it equals $+\infty$ when $\int f^+=\infty$ and $\int f^+-\int f^-$ (computed in `EReal`, hence $-\infty$ when only $\int f^-$ is infinite) otherwise; both parts are lower Lebesgue integrals of $[0,\infty]$-valued functions. Borel measurability of $f$ is with respect to the Borel σ-algebra of the product topology on $X\times Y$. Boundedness is by a real constant, since every `EReal`-valued function is bounded by $\pm\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 148, Proposition 7.31; integral as in Eq. (43) of Chapter 7, p. 139

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

namespace BertsekasShreve.SemicontSelection

open MeasureTheory TopologicalSpace

/-- Proposition 7.31 (Bertsekas & Shreve, p. 148). Let `X`, `Y` be separable metrizable spaces,
`q(dy|x)` a continuous stochastic kernel on `Y` given `X`, and `f : X × Y → R*` Borel-measurable.
Let `λ(x) = ∫ f(x, y) q(dy|x)` (the extended integral (43) of Chapter 7, `∫ f⁺ − ∫ f⁻` with `∞ − ∞ = ∞`, which is `DupacovaWets.Consistency.expect`).
(a) If `f` is lower semicontinuous and bounded below, so is `λ`.
(b) If `f` is upper semicontinuous and bounded above, so is `λ`. -/
theorem prop7_31_semicontinuous_integral {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : X × Y → EReal)
    (hf : @Measurable (X × Y) EReal (borel (X × Y)) _ f) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ z, (b : EReal) ≤ f z) →
      LowerSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, (b : EReal) ≤ DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ z, f z ≤ (b : EReal)) →
      UpperSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y)) ≤ (b : EReal)) := by sorry

end BertsekasShreve.SemicontSelection
