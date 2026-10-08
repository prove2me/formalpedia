-- Prove2me | Theorems.Thm_FoundationsML_Regression_finite_hypothesis_regression_bound_v2
-- name    : FoundationsML.Regression.finite_hypothesis_regression_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:41.874758+00:00
-- url     : https://prove2.me/theorems/e6338c2c-f6bd-40f0-9c6c-de1d766f67a8
-- title:
--   Theorem 11.1 — finite-hypothesis-set regression bound ($m\ge1$)
-- statement:
--   **Statement (Theorem 11.1, p. 268, PDF p. 285).** Let $L$ be a non-negative loss function bounded by $M$. Assume $H$ is finite and nonempty. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, for all $h\in H$:
--   $$R(h) \le \hat R_S(h) + M\sqrt{\frac{\log|H|+\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$, where Lean's $x/0=0$ zeroes the empirical error and the deviation term and the bound is false. Now $m\ge1$ and $\delta\in(0,1)$, the book's standing conventions. Unchanged: $L\in[0,M]$ (the chapter's $L:Y\times Y\to\mathbb R_+$ bounded by $M$, on which the constant $M$ of Hoeffding's step depends) and the standing measurability of $L$ and of every $h\in H$, which make the integrands of $R(h)$ measurable and, being bounded, integrable.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 268, Theorem 11.1 (PDF p. 285)

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError

open MeasureTheory

namespace FoundationsML.Regression

/-- Theorem 11.1 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 268, PDF p. 285). Let `L` be a (non-negative) loss function bounded by `M`.
Assume the hypothesis set `H` is finite (and nonempty). Then, for any `δ > 0`, with
probability at least `1 − δ` over an i.i.d. sample of size `m ≥ 1`, for all `h ∈ H`:
`R(h) ≤ R̂_S(h) + M sqrt((log|H| + log(1/δ))/(2m))`.

**Formalization Note.** Replaces `finite_hypothesis_regression_bound`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`). Now `m ≥ 1` and `δ ∈ (0,1)`, the
book's standing conventions. Everything else is unchanged: `hLnn`/`hLb` put `L` in `[0,M]`
(the chapter's `L : Y×Y → ℝ_+` bounded by `M`, on which the exact constant `M` in Hoeffding's
step depends); `hL_meas`/`hH_meas` are the book's standing measurability convention, which
make the integrands of `GeneralizationError` measurable and (being bounded) integrable. -/
theorem finite_hypothesis_regression_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Finset (X → ℝ)) (hHne : H.Nonempty) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt ((Real.log H.card + Real.log (1 / δ)) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
