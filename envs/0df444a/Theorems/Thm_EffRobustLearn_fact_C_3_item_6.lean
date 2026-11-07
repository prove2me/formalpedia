-- Prove2me | Theorems.Thm_EffRobustLearn_fact_C_3_item_6
-- name    : EffRobustLearn.fact_C_3_item_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:11.643127+00:00
-- url     : https://prove2.me/theorems/6fcbbcdd-7e08-4c0f-8f8f-e04e502c4cb1
-- title:
--   Fact C.3 item 6 — two-sided uniform deviation via Rademacher complexity (corrected: measurable, pointwise separable $F$)
-- statement:
--   Let $F$ be a class of measurable functions with values in a unit interval $[a,a+1]$, pointwise separable, let $D$ be a distribution, $|S|\ge1$ and $\delta\in(0,1)$. With probability at least $1-\delta$,
--   $$\sup_{f\in F}\Big|\mathbb E_{x\sim D}[f(x)]-\frac1{|S|}\sum_{i=1}^{|S|}f(x_i)\Big|\le2R_{|S|,D}(F)+\sqrt{\frac{\log(2/\delta)}{2|S|}}.$$
--
--   Differences from the source:
--   - correction: any class $F$ on a unit interval → measurable functions and pointwise separable; reason: the printed statement is false for $X=\omega_1$ with the countable–cocountable measure and $F$ = indicators of initial segments $[0,\alpha]$: every $f$ has mean $0$ and is $1$ on the whole sample for large $\alpha$, so the supremum is $1$ on every sample, while the Rademacher quantity is at most $C\sqrt{1/n}$ at every sample and so the right side is below $1$ for large $n$
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the measure of the bad set $\le\delta$, an outer measure if the set is not measurable; reason: same event; the bound on the measure is the strongest reading
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact C.3 item 6, p.41 (PDF p.42), cited from [MRT18, Theorem 3.3]

import Mathlib
import Definitions.Def_EffRobustLearn_rademacherD
import Definitions.Def_EffRobustLearn_PointwiseSeparableReal

open MeasureTheory

namespace EffRobustLearn

/-- Fact C.3 item 6, p.41 (arXiv:2609.17655, held version, sha256 312a0857…), cited from [MRT18, Theorem 3.3]: for a class `F` with values in a unit interval `[a, a + 1]`, with probability at least `1 - δ`,
`sup_{f∈F} |E_{x∼D} f(x) - (1/|S|) ∑_i f(x_i)| ≤ 2 R_{|S|,D}(F) + √(log(2/δ)/(2|S|))`.

**Formalization Note.** The probability is the `D^n` measure of the bad set, an outer measure if the set is not measurable. Measurable functions and pointwise separability are the correction: without them the
supremum need not be a random variable and `R` may be the junk value `0`. The integrals here are of bounded measurable functions. -/
theorem fact_C_3_item_6 {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (F : Set (X → ℝ)) (a : ℝ) (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a (a + 1))
    (hmeas : ∀ f ∈ F, Measurable f) (hsep : PointwiseSeparableReal F) (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => D)
      {s | 2 * rademacherD D n F + Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        sSup ((fun f : X → ℝ => |∫ x, f x ∂D - (1 / (n : ℝ)) * ∑ i, f (s i)|) '' F)} ≤
      ENNReal.ofReal δ := by sorry

end EffRobustLearn
