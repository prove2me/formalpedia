-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_theorem_A_1
-- name    : BartlettBousquetMendelson.LocalRad.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:02:33.576339+00:00
-- url     : https://prove2.me/theorems/7de57348-cd8d-4d78-a087-9fa88fcb45d8
-- title:
--   Theorem A.1: Bousquet's version of Talagrand's inequality
-- statement:
--   Let $c>0$, let $X_1,\dots,X_n$ be iid with law $P$, and let $\mathcal F$ be a class of measurable functions with $\mathbb Ef=0$ and $\|f\|_\infty\le c$ for all $f\in\mathcal F$. Let $\sigma>0$ with $\sigma^2\ge\sup_{f\in\mathcal F}\mathrm{Var}[f(X_i)]$. Put
--
--   $$
--   Z=\sup_{f\in\mathcal F}\sum_{i=1}^nf(X_i),\qquad h(x)=(1+x)\log(1+x)-x,\qquad v=n\sigma^2+2c\,\mathbb EZ.
--   $$
--
--   Then for every $x\ge0$:
--
--   1. $$\Pr(Z\ge\mathbb EZ+x)\le\exp\Big(-v\,h\Big(\frac x{cv}\Big)\Big);$$
--   2. with probability at least $1-e^{-x}$, $$Z\le\mathbb EZ+\sqrt{2xv}+\frac{cx}3.$$
--
--   This concentration inequality for the supremum of an empirical process is the probabilistic engine of Theorem 2.1.
--
--   Differences from the source:
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable and IsPointwiseMeasurableClass F; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - reading: ‖f‖∞ ≤ c → |f| ≤ c P-almost everywhere; reason: the L∞(P) norm; it contains the reading as a bound at every point, so it is the more general reading
--   - encoding: σ² ≥ sup_{f∈F} Var[f(Xᵢ)] → Var f ≤ σ² for every f ∈ F; reason: equivalent
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Theorem A.1, p. 34 (cited from Bousquet [7, 8]) (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass

open MeasureTheory ProbabilityTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Theorem A.1 (Bousquet's version of Talagrand's inequality, cited from [7, 8]).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Theorem A.1, p. 34: "Let c > 0, let Xi be independent random variables distributed according
to P and let F be a set of functions from X to R. Assume that all functions f in F satisfy Ef = 0
and ∥f∥∞ ≤ c. Let σ be a positive real number such that σ^2 ≥ sup_{f∈F} Var[f(Xi)]. Then, for any
x ≥ 0, Pr(Z ≥ EZ + x) ≤ exp(−vh(x/(cv))), where Z = sup_{f∈F} Σ_{i=1}^n f(Xi),
h(x) = (1 + x)log(1 + x) − x and v = nσ^2 + 2cEZ. Also, with probability at least 1 − e^{−x},
Z ≤ EZ + √(2xv) + cx/3."

Let `X₁, …, Xₙ` be iid `P` (`n ≥ 1`), `F` a class of measurable functions with `Pf = 0`,
`|f| ≤ c` `P`-a.e. and `Var f ≤ σ²` (`c, σ > 0`). With `Z = sup_{f∈F} Σᵢ f(Xᵢ)`,
`v = nσ² + 2c EZ` and `h(u) = (1 + u) log(1 + u) − u`, for every `x ≥ 0`:
(1) `Pr(Z ≥ EZ + x) ≤ exp(−v h(x/(cv)))`; (2) `Pr(Z ≤ EZ + √(2xv) + cx/3) ≥ 1 − e^{−x}`.

**Formalization Note.** `‖f‖∞ ≤ c` is read as the `L∞(P)` bound `|f| ≤ c` `P`-almost everywhere
(this contains the reading as a bound for every point).
"σ² ≥ sup Var" is `Var f ≤ σ²` for every `f ∈ F`. Measurability (p. 3 and p. 7, Reading M):
each `f` measurable and `F` pointwise measurable (`IsPointwiseMeasurableClass`), so `Z` is a
countable supremum off a null set, measurable and a.e. bounded by `nc`. The sample space is `Fin n → X` with
`Measure.pi`. For empty `F`, Lean's `Z` is `0` (the paper's is `−∞`) and both claims hold
trivially. -/
theorem theorem_A_1 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (n : ℕ) (hn : 0 < n) (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hmean : ∀ f ∈ F, ∫ y, f y ∂P = 0) (hbound : ∀ f ∈ F, ∀ᵐ y ∂P, |f y| ≤ c)
    (hvar : ∀ f ∈ F, variance f P ≤ σ ^ 2) :
    let μ : Measure (Fin n → X) := Measure.pi fun _ : Fin n => P
    let Z : (Fin n → X) → ℝ := fun ω => ⨆ f : F, ∑ i, f.1 (ω i)
    let EZ : ℝ := ∫ ω, Z ω ∂μ
    let v : ℝ := n * σ ^ 2 + 2 * c * EZ
    let h : ℝ → ℝ := fun u => (1 + u) * Real.log (1 + u) - u
    ∀ x : ℝ, 0 ≤ x →
      μ.real {ω | EZ + x ≤ Z ω} ≤ Real.exp (-(v * h (x / (c * v)))) ∧
      1 - Real.exp (-x) ≤ μ.real {ω | Z ω ≤ EZ + Real.sqrt (2 * x * v) + c * x / 3} := by sorry

end BartlettBousquetMendelson.LocalRad
