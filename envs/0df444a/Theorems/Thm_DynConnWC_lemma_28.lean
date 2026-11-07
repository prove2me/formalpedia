-- Prove2me | Theorems.Thm_DynConnWC_lemma_28
-- name    : DynConnWC.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:44.909135+00:00
-- url     : https://prove2.me/theorems/23fe11dc-74e7-46f3-8724-cea3548ad2cf
-- title:
--   Lemma 28 — $E[(Y-1)^4]\le1-\lambda/2$ for sparse sums
-- statement:
--   Let $Y$ be the sum of countably many (in particular finitely many) mutually independent random variables with values in $\{0,1\}$, with $\lambda=E[Y]\le1/4$ finite. Then $(Y-1)^4$ is integrable and
--   $$E[(Y-1)^4]\le1-\frac\lambda2.$$
--   This gives the single-tree factor in the product bound of Lemma 11.
--
--   Differences from the source:
--   - encoding: a sum of independent 0/1 random variables with $E[Y]=\lambda$ → measurable real functions on a probability space, each pointwise $0$ or $1$, with `iIndepFun`; $Y$ an integrable function that is almost surely their sum, $\lambda=\int Y$; reason: $E[Y]=\lambda$ finite is integrability of $Y$, and the sum converges almost surely because its expectation is finite
--   - generalization: a sum of independent 0/1 random variables (the source's use has finitely many) → countably many variables; reason: for a finite family take $Y=\sum_iX_i$, which meets every hypothesis, so the statement specializes to the finite case
--   - encoding: $E[(Y-1)^4]$ → the conclusion also states that $(Y-1)^4$ is integrable; reason: otherwise Lean's Bochner integral would be the junk value $0$; the fourth moment is finite in the source's setting
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 28, p.26 (PDF 27)

import Mathlib

set_option autoImplicit false

namespace DynConnWC

open MeasureTheory ProbabilityTheory in
/-- **Lemma 28 (A sparse fourth moment).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.26 (PDF 27).
"If Y is a sum of independent 0/1 random variables with E[Y] = λ ≤ 1/4, then E[(Y − 1)⁴] ≤ 1 − λ/2."

**Formalization Note.** Countably many (in particular finitely many) variables `X i` on a probability
space, mutually independent, each taking only the values `0` and `1`. `Y` is their sum: almost surely
`Σ_i X i = Y`. `E[Y] = λ` is finite, so `Y` is integrable and `λ = ∫ Y`. The conclusion also states that
`(Y − 1)⁴` is integrable, so its Bochner integral is the true expectation and not Lean's junk value `0`.
For finitely many variables take `Y = Σ_i X i`; the hypotheses then hold automatically. The empty sum
(`λ = 0`) is allowed. -/
theorem lemma_28 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hind : iIndepFun X μ)
    (Y : Ω → ℝ) (hY : ∀ᵐ ω ∂μ, HasSum (fun i => X i ω) (Y ω)) (hYint : Integrable Y μ)
    (hlam : ∫ ω, Y ω ∂μ ≤ 1 / 4) :
    Integrable (fun ω => (Y ω - 1) ^ 4) μ ∧
      ∫ ω, (Y ω - 1) ^ 4 ∂μ ≤ 1 - (∫ ω, Y ω ∂μ) / 2 := by sorry

end DynConnWC
