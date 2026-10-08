-- Prove2me | Theorems.Thm_AddLogReg_Discrete_result_1
-- name    : AddLogReg.Discrete.result_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:35.386987+00:00
-- url     : https://prove2.me/theorems/7a042720-6adc-42b4-b9cd-49a48bb9a554
-- title:
--   Result 1, p. 346 — population Discrete AdaBoost takes Newton-like steps with exact line search on E(e^{−yF(x)})
-- statement:
--   **Result 1.** The Discrete AdaBoost algorithm (population version) builds an additive logistic regression model via Newton-like updates for minimizing $E(e^{-yF(x)})$.
--
--   Let $\nu$ be the law of $(x, y)$ on $X \times \{-1, 1\}$ and let $F : X \to \mathbb R$ be a measurable current estimate with $J(F) = E(e^{-yF(x)}) < \infty$. Write $E_w$ for weighted (conditional) expectations with weight $w(x, y) = e^{-yF(x)}$, $f^\ast$ for the classifier (18), equal to $1$ where $E_w(y \mid x) > 0$ and $-1$ elsewhere, and $\mathrm{err} = E_w[1_{[y \neq f(x)]}]$ for the weighted error of a classifier $f$. One step of the algorithm has the following three properties, which make "Newton-like updates" precise as in the paper's proof.
--
--   1. **Newton-like choice of $f$.** For every $c > 0$, every $x$ and every $s \in \{-1, 1\}$,
--   $$E_w\Big(1 - ycf^\ast(x) + \frac{c^2}{2} \,\Big|\, x\Big) \le E_w\Big(1 - ycs + \frac{c^2}{2} \,\Big|\, x\Big),$$
--   i.e. $f^\ast$ minimizes, pointwise over $\{-1,1\}$, the second-order approximation (16) of the criterion.
--   2. **Exact line search.** For every measurable $\pm 1$-valued $f$ with $0 < \mathrm{err} < 1$, the coefficient $c = \frac12 \log((1 - \mathrm{err})/\mathrm{err})$ of (20) minimizes $J(F + c' f)$ over $c' \in \mathbb R$:
--   $$J(F + cf) \le J(F + c'f) \quad \text{for all } c' \in \mathbb R .$$
--   3. **Same weights as Algorithm 1.** For every $\pm 1$-valued $f$, with $c$ as in 2, every $x$ and every $y$,
--   $$e^{-yF(x)}\, e^{-cf(x)y} = e^{-c} \cdot e^{-yF(x)} \exp\Big(\log\frac{1 - \mathrm{err}}{\mathrm{err}}\; 1_{[y \neq f(x)]}\Big),$$
--   so the population update $F \leftarrow F + cf$ reweights by $w \leftarrow w e^{-cf(x)y}$, which after renormalization is Discrete AdaBoost's update with $c_m = \log((1 - \mathrm{err})/\mathrm{err}) = 2c$.
--
--   Since Algorithm 1 adds $c_m f_m = 2 c f_m$, its function is twice the population $F$; the two have the same sign, so the output classifiers agree.
--
--   **Formalization Note** Labels are Booleans with $y = \pm 1$; the criterion $J$ is a lower integral in $[0, \infty]$ and is compared there. $J(F) < \infty$ and measurability of $F$ and $f$ are the standing conditions under which the weighted expectations are defined. $0 < \mathrm{err} < 1$ is needed for the logarithm in (20). The conditional expectation given $x$ is the integral against the disintegration kernel of $\nu$; property 1 holds for every $x$.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 346, Result 1, and its proof pp. 346–347; p. 338, Algorithm 1

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- Result 1, p. 346 (population version), as its proof (pp. 346–347) makes precise. One step of
Discrete AdaBoost from the current estimate `F` (measurable, with `J(F) < ∞`):
1. (Newton-like choice of `f`, (16)–(18)) for every `c > 0` and every `x`, the classifier (18)
   minimizes the quadratic approximation `E_w(1 − ycs + c²/2 | x)` over `s ∈ {−1, 1}`;
2. (exact line search, (20)) for every measurable `f` with values in `{−1, 1}` and
   `0 < err < 1`, `c = ½ log((1 − err)/err)` minimizes `c' ↦ AddLogReg.ExpCrit.J(F + c'f)`;
3. (weight update) the weight `w(x, y) = e^{−yF(x)}` augmented by `e^{−cf(x)y}` equals the
   constant `e^{−c}` times Algorithm 1's update `w(x, y) exp(log((1 − err)/err) 1_{[y ≠ f(x)]})`,
   so the two coincide after renormalization. -/
theorem result_1 {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) :
    (∀ c : ℝ, 0 < c → ∀ x : X, ∀ s : ℝ, (s = 1 ∨ s = -1) →
      AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * newtonClassifier ν F x + c ^ 2 / 2) x ≤
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 / 2) x) ∧
    (∀ f : X → ℝ, Measurable f → IsPMOne f → 0 < err ν F f → err ν F f < 1 →
      ∀ c' : ℝ, AddLogReg.ExpCrit.J ν (F + lineSearchCoeff (err ν F f) • f) ≤ AddLogReg.ExpCrit.J ν (F + c' • f)) ∧
    (∀ f : X → ℝ, IsPMOne f → ∀ (x : X) (b : Bool),
      Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) * Real.exp (-(lineSearchCoeff (err ν F f) * f x * AddLogReg.ExpCrit.sgn b)) =
        Real.exp (-lineSearchCoeff (err ν F f)) * (Real.exp (-(AddLogReg.ExpCrit.sgn b * F x)) *
          Real.exp (Real.log ((1 - err ν F f) / err ν F f) * (if AddLogReg.ExpCrit.sgn b ≠ f x then 1 else 0)))) := by sorry

end AddLogReg.Discrete
