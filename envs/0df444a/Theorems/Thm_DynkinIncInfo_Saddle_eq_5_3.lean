-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_eq_5_3
-- name    : DynkinIncInfo.Saddle.eq_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:03.539006+00:00
-- url     : https://prove2.me/theorems/63cc080c-f7ae-4546-aa9a-f1b60d5fa0be
-- title:
--   (5.1)–(5.4), p. 12 — Z_t = ln X_t + (σ²/δ0) ln(Y_t/(1 − Y_t)) = z + kt and X_t = F(Z_t, Y_t)
-- statement:
--   Let $x>0$, $y\in(0,1)$, and set $z=\ln x+\frac{\sigma^2}{\delta_0}\ln\frac{y}{1-y}$ and $k=r-\frac{\sigma^2}{2}-\frac{\delta_0}{2}$. For every $t\ge0$ (and every outcome),
--   $$\ln X_t+\frac{\sigma^2}{\delta_0}\ln\frac{Y_t}{1-Y_t}=z+kt,\qquad X_t=F(z+kt,\,Y_t),$$
--   where $X=S^x$ is the asset, $Y$ the filter and $F(z,y)=e^z\big(\frac{1-y}{y}\big)^{\sigma^2/\delta_0}$.
--
--   The process $Z_t$ is deterministic: it plays the role of time and turns the two-dimensional problem into a parabolic one.
--
--   **Formalization Note.** With the explicit encoding the identities hold for every $t$ and every outcome, which is stronger than the paper's almost-sure statement. This item is the bridge between the paper's $(Z,Y)$ coordinates and the original-space encoding.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 12, (5.1)–(5.5)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 12, (5.1)–(5.4): for `(x, y) ∈ (0, ∞) × (0, 1)` and
`z = ln x + (σ²/δ0) ln(y/(1 − y))`, the process `Z_t = ln X_t + (σ²/δ0) ln(Y_t/(1 − Y_t))`
satisfies `Z_t = z + kt` with `k = r − σ²/2 − δ0/2` (5.3), and `X_t = F(Z_t, Y_t)` (5.4).

**Formalization Note.** With `X := S` and the closed-form filter `Y`, (5.3) and (5.4) hold for
every `t` and every `ω` (stronger than the paper's `ℙ`-a.s.); this item is the bridge between
the paper's `(Z, Y)` coordinates and the original-space encoding. Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem eq_5_3 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (t : ℝ≥0) (ω : Ω) :
    Real.log (S p st x y t ω)
        + p.σ ^ 2 / p.δ0 * Real.log (Y p st x y t ω / (1 - Y p st x y t ω))
      = Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ) ∧
    S p st x y t ω
      = F p (Real.log x + p.σ ^ 2 / p.δ0 * Real.log (y / (1 - y)) + k p * (t : ℝ))
          (Y p st x y t ω) := by sorry

end DynkinIncInfo.Saddle
