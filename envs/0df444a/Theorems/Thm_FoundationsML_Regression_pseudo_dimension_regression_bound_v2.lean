-- Prove2me | Theorems.Thm_FoundationsML_Regression_pseudo_dimension_regression_bound_v2
-- name    : FoundationsML.Regression.pseudo_dimension_regression_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:48.952117+00:00
-- url     : https://prove2.me/theorems/439dfc1a-6cf9-4da5-af8e-dad567c0f831
-- title:
--   Theorem 11.8 — pseudo-dimension regression bound ($m\ge1$)
-- statement:
--   **Statement (Theorem 11.8, p. 273, PDF p. 290).** Let $H$ be a family of (measurable) real-valued functions and $G=\{(x,y)\mapsto L(h(x),y):h\in H\}$. Assume $\mathrm{Pdim}(G)=d$ and $L$ is non-negative and bounded by $M$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample $S$ of size $m\ge1$, $m\ge d$, for all $h\in H$:
--   $$R(h) \le \hat R_S(h) + M\sqrt{\frac{2d\log(em/d)}{m}} + M\sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $d=m=0$, where every sample-dependent term is Lean's $x/0=0$ and the bound is false. Now $m\ge1$ and $\delta\in(0,1)$ (standing conventions); $d\le m$ is kept as the domain of Corollary 3.18's growth-function bound through which the proof passes. For $d=0$ with $m\ge1$ the pseudo-dimension term is Lean's $\sqrt0=0$, which is harmless: $\mathrm{Pdim}(G)=0$ forces $G$ to consist of a single function and the bound reduces to Hoeffding's. Measurability of $L$ and of every $h\in H$ is the standing convention, making the integrands of $R(h)$ measurable and, being bounded, integrable.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 273, Theorem 11.8 (PDF p. 290)

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_LossComposedFamily
import Definitions.Def_FoundationsML_Regression_PseudoDim

open MeasureTheory

namespace FoundationsML.Regression

/-- Theorem 11.8 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 273, PDF p. 290). Let `H` be a family of real-valued functions and
`G = {(x,y) ↦ L(h(x),y) : h ∈ H}`. Assume `Pdim(G) = d` and `L` is non-negative and bounded by
`M`. Then, for any `δ > 0`, with probability at least `1 − δ` over an i.i.d. sample `S` of
size `m ≥ 1` (`m ≥ d`), for all `h ∈ H`:
`R(h) ≤ R̂_S(h) + M sqrt(2d log(em/d)/m) + M sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `pseudo_dimension_regression_bound`, which allowed
`d = m = 0` (every sample-dependent term is then Lean's `x / 0 = 0`). Now `m ≥ 1` and
`δ ∈ (0,1)` (standing conventions); `d ≤ m` is kept as the domain of Corollary 3.18's
growth-function bound through which the proof passes. `hL_meas`/`hH_meas` are the book's
standing measurability convention, making the integrands of `GeneralizationError` measurable
and (being bounded) integrable. -/
theorem pseudo_dimension_regression_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (d : ℕ) (hPdim : PseudoDim (LossComposedFamily L H) d)
    (m : ℕ) (hm : 0 < m) (hdm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
