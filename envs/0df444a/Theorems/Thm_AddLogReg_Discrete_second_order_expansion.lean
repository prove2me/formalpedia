-- Prove2me | Theorems.Thm_AddLogReg_Discrete_second_order_expansion
-- name    : AddLogReg.Discrete.second_order_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:51.358458+00:00
-- url     : https://prove2.me/theorems/c235302b-24a6-4b29-9cd3-c28a44f288f3
-- title:
--   Proof of Result 1, p. 346 — second-order expansion E_w(e^{−cyf(x)}|x) ≈ E_w(1 − ycf(x) + c²/2|x)
-- statement:
--   In the population setting of Discrete AdaBoost, fix a current estimate $F$, a point $x$ and a value $s = f(x) \in \{-1, 1\}$. With weight $w(x, y) = e^{-yF(x)}$, consider
--   $$g(c) = E_w\big(e^{-cys} \mid x\big) = \frac{E\big(e^{-y(F(x) + cs)} \mid x\big)}{E\big(e^{-yF(x)} \mid x\big)}, \qquad c \in \mathbb R.$$
--   Then $g(0) = 1$, $g$ is differentiable with $g'(c) = -E_w\big(ys\, e^{-cys} \mid x\big)$, so $g'(0) = -E_w(ys \mid x)$, and $g'$ is differentiable at $0$ with $g''(0) = 1$. Consequently the second-order Taylor polynomial of $g$ at $0$ is
--   $$E_w\Big(1 - ycs + \frac{c^2 y^2 s^2}{2} \,\Big|\, x\Big) = E_w\Big(1 - ycs + \frac{c^2}{2} \,\Big|\, x\Big) = g(0) + g'(0)\, c + \frac{c^2}{2},$$
--   using $y^2 = s^2 = 1$.
--
--   This is the second-order expansion of $J(F + cf)$ about $f(x) = 0$ in the proof of Result 1, conditionally on $x$ and divided by $E(e^{-yF(x)} \mid x)$; it is the quadratic criterion minimized in (16).
--
--   **Formalization Note** The page's "≈" is read as "is the second-order Taylor polynomial in $c$"; the derivatives are stated with `HasDerivAt`, never with a bare `deriv`. The expansion is stated for each fixed $x$ and $s$, as the page minimizes pointwise.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 346, proof of Result 1, first display

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- Proof of Result 1, p. 346: for fixed `x` and `s = f(x) ∈ {−1, 1}`, the weighted conditional
criterion `g(c) = E_w(e^{−cys} | x)` has `g(0) = 1`, first derivative `−E_w(ys | x)` at `0` and
second derivative `E_w(y²s² | x) = 1` at `0`; its second-order Taylor polynomial is
`E_w(1 − ycs + c²y²s²/2 | x) = E_w(1 − ycs + c²/2 | x)`. -/
theorem second_order_expansion {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (x : X) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    let g : ℝ → ℝ := fun c => AddLogReg.ExpCrit.wCondExp ν F (fun _ b => Real.exp (-(c * AddLogReg.ExpCrit.sgn b * s))) x
    let g' : ℝ → ℝ := fun c =>
      -AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * s * Real.exp (-(c * AddLogReg.ExpCrit.sgn b * s))) x
    g 0 = 1 ∧ (∀ c : ℝ, HasDerivAt g (g' c) c) ∧
      g' 0 = -AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * s) x ∧ HasDerivAt g' 1 0 ∧
      ∀ c : ℝ,
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 * AddLogReg.ExpCrit.sgn b ^ 2 * s ^ 2 / 2) x =
            AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 / 2) x ∧
          AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 / 2) x =
            g 0 + g' 0 * c + 1 * c ^ 2 / 2 := by sorry

end AddLogReg.Discrete
