-- Prove2me | Theorems.Thm_AddLogReg_Discrete_eq_17_18
-- name    : AddLogReg.Discrete.eq_17_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:26.573332+00:00
-- url     : https://prove2.me/theorems/880e436c-d46e-4675-a564-2d9417f21fb3
-- title:
--   (17)–(18), p. 347 — for c > 0, minimizing (16) ⇔ maximizing E_w[yf(x)]; solution f(x) = 1 iff E_w(y|x) > 0
-- statement:
--   In the population setting of Discrete AdaBoost, let $F$ be measurable with $J(F) = E(e^{-yF(x)}) < \infty$, and write $E_w$ for weighted expectations with weight $w(x, y) = e^{-yF(x)}$. Then:
--
--   1. for every $c > 0$, every $x$ and all $s, t \in \{-1, 1\}$,
--   $$E_w\Big(1 - ycs + \frac{c^2}{2} \,\Big|\, x\Big) \le E_w\Big(1 - yct + \frac{c^2}{2} \,\Big|\, x\Big) \iff E_w(yt \mid x) \le E_w(ys \mid x),$$
--   so minimizing (16) over $f(x) \in \{-1, 1\}$ is maximizing $E_w(yf(x) \mid x)$;
--   2. $E_w(y \mid x) = P_w(y = 1 \mid x) - P_w(y = -1 \mid x)$ for every $x$, where $P_w(y = \pm 1 \mid x) = E_w(1_{[y = \pm 1]} \mid x)$;
--   3. the classifier (18),
--   $$f^\ast(x) = \begin{cases} 1, & \text{if } E_w(y \mid x) > 0, \\ -1, & \text{otherwise}, \end{cases}$$
--   satisfies $E_w(ys \mid x) \le E_w(yf^\ast(x) \mid x)$ for every $x$ and every $s \in \{-1, 1\}$;
--   4. $f^\ast$ maximizes (17): $E_w[yf(x)] \le E_w[yf^\ast(x)]$ for every measurable $f$ with values in $\{-1, 1\}$.
--
--   This identifies the Newton-like step of population Discrete AdaBoost: the classifier that minimizes the quadratic approximation of the exponential criterion.
--
--   **Formalization Note** Ties $E_w(y \mid x) = 0$ are sent to $-1$, as the page's "otherwise" does. The finiteness $J(F) < \infty$ is the standing assumption under which $E_w$ is defined.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 347, (16), (17), (18)

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- (16)–(18), p. 347: for `c > 0`, minimizing `E_w(1 − ycs + c²/2 | x)` over `s ∈ {−1, 1}` is
equivalent to maximizing `E_w(ys | x)`; the maximizer is (18), `f(x) = 1` if
`E_w(y | x) = P_w(y = 1 | x) − P_w(y = −1 | x) > 0` and `−1` otherwise; and this `f` maximizes
(17), `E_w[yf(x)]`, over all measurable `f` with values in `{−1, 1}`. -/
theorem eq_17_18 {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) :
    (∀ c : ℝ, 0 < c → ∀ x : X, ∀ s t : ℝ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
      (AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * s + c ^ 2 / 2) x ≤
          AddLogReg.ExpCrit.wCondExp ν F (fun _ b => 1 - AddLogReg.ExpCrit.sgn b * c * t + c ^ 2 / 2) x ↔
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * t) x ≤ AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * s) x)) ∧
    (∀ x : X, AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b) x =
      AddLogReg.ExpCrit.wCondExp ν F (fun _ b => if b = true then 1 else 0) x -
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => if b = false then 1 else 0) x) ∧
    (∀ x : X, ∀ s : ℝ, (s = 1 ∨ s = -1) →
      AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * s) x ≤
        AddLogReg.ExpCrit.wCondExp ν F (fun _ b => AddLogReg.ExpCrit.sgn b * newtonClassifier ν F x) x) ∧
    (∀ f : X → ℝ, Measurable f → IsPMOne f →
      wExp ν F (fun x b => AddLogReg.ExpCrit.sgn b * f x) ≤
        wExp ν F (fun x b => AddLogReg.ExpCrit.sgn b * newtonClassifier ν F x)) := by sorry

end AddLogReg.Discrete
