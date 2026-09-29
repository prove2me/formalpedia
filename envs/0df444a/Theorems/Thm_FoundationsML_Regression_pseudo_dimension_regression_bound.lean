-- Prove2me | Theorems.Thm_FoundationsML_Regression_pseudo_dimension_regression_bound
-- name    : FoundationsML.Regression.pseudo_dimension_regression_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:10:56.149288+00:00
-- url     : https://prove2.me/theorems/573cbfd0-b9f2-4969-aa62-2ca3ea7083a0
-- title:
--   Theorem 11.8 — Pseudo-dimension regression bound
-- statement:
--   **Statement (Theorem 11.8, p. 273, PDF p. 290).** Let $H$ be a family of real-valued
--   functions and $G=\{(x,y)\mapsto L(h(x),y):h\in H\}$. Assume $\mathrm{Pdim}(G)=d$ and $L$
--   is non-negative and bounded by $M$. Then, for any $\delta>0$, with probability at least
--   $1-\delta$ over an i.i.d. sample $S$ of size $m$, for all $h\in H$:
--   $R(h) \le \hat R_S(h) + M\sqrt{2d\log(em/d)/m} + M\sqrt{\log(1/\delta)/(2m)}$. The
--   chapter's second, independent technique (pseudo-dimension, reducing regression to
--   classification via Eq. 11.5's expectation-as-integrated-tail identity), structurally
--   parallel to chunk `03`'s Corollary 3.19 but proved by a distinct pseudo-dimension argument.
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
size `m`, for all `h ∈ H`: `R(h) ≤ R̂_S(h) + M sqrt(2d log(em/d)/m) + M sqrt(log(1/δ)/(2m))`.

**Formalization Note.** `hH_meas`/`hL_meas` guard `GeneralizationError`'s Bochner integral
against trap 2, for the same reason as `rademacher_regression_bound`/
`finite_hypothesis_regression_bound`. -/
theorem pseudo_dimension_regression_bound
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (d : ℕ) (hPdim : PseudoDim (LossComposedFamily L H) d)
    (m : ℕ) (hdm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Regression
