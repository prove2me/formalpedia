-- Prove2me | Theorems.Thm_DirectTradeCoffee_proposition_1
-- name    : DirectTradeCoffee.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:13.153051+00:00
-- url     : https://prove2.me/theorems/21be15ac-16d0-4f54-a100-17df8f066e72
-- title:
--   Proposition 1, pp.10–11 — the second-stage solution $q^*=\min\{q^\circ(\varphi),Qy\}$, its price and value
-- statement:
--   Fix $Q\ge0$, a yield $y>0$ and a blend price $\varphi$, and write $x = e^{v-1}/(e^{b\varphi}+e^{v_B})$. The second-stage problem has the unique solution
--
--   $$
--   q^* = \min\left\{ W(x)\,(1+W(x))^{-1},\ Qy \right\}.
--   $$
--
--   For $Q>0$ its clearing price is
--
--   $$
--   p(q^*) = \begin{cases} \varphi + \dfrac1b\left(1+\ln\left[x\,\dfrac{1-Qy}{Qy}\right]\right), & q^*=Qy,\\[2mm] \varphi + \dfrac1b\,(1+W(x)), & q^*<Qy, \end{cases}
--   $$
--
--   and the optimal value is
--
--   $$
--   \pi^*(Q,\varphi,y) = \begin{cases} \dfrac1b\left(1+\ln\left[x\,\dfrac{1-Qy}{Qy}\right]\right)Qy + (\varphi-c)Qy - k(Q), & q^*=Qy,\\[2mm] \dfrac1b\,W(x) + (\varphi-c)Qy - k(Q), & q^*<Qy. \end{cases}
--   $$
--
--   This replaces the inner optimization of the two-stage problem by an explicit formula: either the supply $Qy$ binds or the roaster sells the unconstrained quantity and downgrades the rest to the blend label.
--
--   Differences from the source:
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - generalization: φ and y realized in the support → any real φ and any y > 0; reason: the maximization uses neither bound; realizations in Ω are instances
--   - reading: "the optimal quantity sold as SL is q*" → q* is optimal and every optimal quantity equals q*; reason: the definite article; the objective is strictly concave
--   - encoding: price cases for every contract acreage → the price claims are for Q > 0; reason: at Q = 0 nothing is sold, no price clears zero demand, and the printed case has ln(1/0)
--   - reading: p.13 illustrates a capacity limit Q_max by k′(Q_max) = ∞ → k is real-valued and continuous on [0, ∞), as p.10 and p.31 assume; reason: the illustration lies outside the model assumption that k is a continuous function; every k of the model is covered
--   - encoding: second-stage constraint 0 ≤ q ≤ 1 → 0 ≤ q < 1; reason: at q = 1 no finite price clears the market and the objective tends to −∞; the maximum and its maximizer are unchanged
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, Proposition 1, pp.10–11

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **Proposition 1**, Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for Specialty
Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, pp.10–11: the second-stage solution.

`q* = min{q°(φ), Qy}` is the unique solution of the second-stage problem, the price `p(q*)` and the
value `π*(Q, φ, y)` are the two printed cases.

**Formalization Note.** `q* = Qy` and `q* < Qy` are the printed case distinctions. The price claim
is for `Q > 0`: at `Q = 0` nothing is sold and the printed formula has `ln(1/0)`. The value claim
at `Q = 0` reads `−k(0)`, because the logarithm term is multiplied by `Qy = 0`. -/
theorem proposition_1 (P : Params) {k : ℝ → ℝ} (hk : IsCost k) (Q φ y : ℝ)
    (hQ : 0 ≤ Q) (hy : 0 < y) :
    IsOptimalQuantity P k Q φ y (min (qo P φ) (Q * y)) ∧
    (∀ q, IsOptimalQuantity P k Q φ y q → q = min (qo P φ) (Q * y)) ∧
    (0 < Q → min (qo P φ) (Q * y) = Q * y →
      price P (min (qo P φ) (Q * y)) φ =
        φ + (1 / P.b) * (1 + Real.log (xArg P φ * ((1 - Q * y) / (Q * y))))) ∧
    (0 < Q → min (qo P φ) (Q * y) < Q * y →
      price P (min (qo P φ) (Q * y)) φ = φ + (1 / P.b) * (1 + lambertW (xArg P φ))) ∧
    (min (qo P φ) (Q * y) = Q * y →
      secondStageValue P k Q φ y =
        (1 / P.b) * (1 + Real.log (xArg P φ * ((1 - Q * y) / (Q * y)))) * (Q * y)
          + (φ - P.c) * (Q * y) - k Q) ∧
    (min (qo P φ) (Q * y) < Q * y →
      secondStageValue P k Q φ y =
        (1 / P.b) * lambertW (xArg P φ) + (φ - P.c) * (Q * y) - k Q) := by sorry

end DirectTradeCoffee
