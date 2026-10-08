-- Prove2me | Theorems.Thm_FoundationsML_Regression_rademacher_regression_bound_v2
-- name    : FoundationsML.Regression.rademacher_regression_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:59.971189+00:00
-- url     : https://prove2.me/theorems/722b6d6e-5aa7-48ab-a456-fbb11573e7ab
-- title:
--   Theorem 11.3 — Rademacher complexity regression bounds (goal; $m\ge1$, bounded $H$)
-- statement:
--   **Statement (Theorem 11.3, p. 270, PDF p. 287).** Let $L$ be non-negative, bounded by $M>0$, and $\mu$-Lipschitz in its first argument, and $H$ a (measurable) hypothesis set mapping into a bounded interval. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, each of the following holds for all $h\in H$:
--   $$\mathbb E[L(h(x),y)] \le \tfrac1m\sum_i L(h(x_i),y_i) + 2\mu R_m(H) + M\sqrt{\tfrac{\log(1/\delta)}{2m}},$$
--   $$\mathbb E[L(h(x),y)] \le \tfrac1m\sum_i L(h(x_i),y_i) + 2\mu\hat R_S(H) + 3M\sqrt{\tfrac{\log(2/\delta)}{2m}}.$$
--   Each inequality holds with probability at least $1-\delta$.
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$). Changes: $m\ge1$, $\delta\in(0,1)$ (standing conventions); $H$ bounded (Definition 3.1's domain for $R_m(H)$; for unbounded $H$ the retired real supremum was junk); the book's footnote 3 (p. 30), measurability of the supremum defining $\hat R_S(H)$, explicit (needed for $R_m(H)$ to be the book's expectation rather than Lean's junk $0$); the corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`). As before, $R_m(H)$ is taken under the marginal $D.\mathrm{map}\,\mathrm{Prod.fst}$ of the inputs, measurability of $L$ and of every $h\in H$ is the standing convention, and the two inequalities are separate probability statements.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 270, Theorem 11.3 (PDF p. 287)

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.Regression

/-- Theorem 11.3 (Rademacher complexity regression bounds; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 270, PDF p. 287).
Let `L` be a non-negative loss bounded by `M > 0` that is `µ`-Lipschitz in its first argument,
and `H` a (bounded, as Definition 3.1 requires) hypothesis set. Then, for any `δ > 0`, with
probability at least `1 − δ` over an i.i.d. sample of size `m ≥ 1`, each of the following
holds for all `h ∈ H`:
`E[L(h(x),y)] ≤ (1/m)∑L(h(x_i),y_i) + 2µ R_m(H) + M sqrt(log(1/δ)/(2m))`, and
`E[L(h(x),y)] ≤ (1/m)∑L(h(x_i),y_i) + 2µ R̂_S(H) + 3M sqrt(log(2/δ)/(2m))`.

**Formalization Note.** Replaces `rademacher_regression_bound`, which allowed `m = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)` (standing
conventions); `H` maps into a bounded interval (`hHb`, Definition 3.1's domain for `R_m(H)`);
the book's footnote 3 (p. 30), that the supremum defining `R̂_S(H)` is measurable, is explicit
(`hHsup`, needed for `R_m(H)` to be the book's expectation rather than Lean's junk `0`); the
corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`, supremum over exactly
`H`) are used. As before, `R_m(H)` is taken under the marginal `D.map Prod.fst` of the inputs,
`hL_meas`/`hH_meas` are the standing measurability convention, and each displayed inequality
holds with probability at least `1 − δ`. -/
theorem rademacher_regression_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * RademacherComplexity (Measure.map Prod.fst D) H m +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * EmpiricalRademacherComplexity H (fun i => (S i).1) +
            3 * M * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
