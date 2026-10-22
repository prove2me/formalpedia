-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_remark_3_3
-- name    : DynkinIncInfo.Saddle.remark_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:19.429373+00:00
-- url     : https://prove2.me/theorems/04c0a9e6-3858-4462-b55d-1ef4b46ad9a5
-- title:
--   Remarks 3.3, p. 8 — the value is strictly positive for x > 0
-- statement:
--   For every initial price $x>0$ and prior $y\in[0,1]$,
--   $$V(x,y)>0.$$
--
--   The paper derives this from the monotonicity of $V$ in $y$ and the positivity of the complete-information value $V_1$ (the case $\mathbb P(D=1)=1$). It implies that the buyer never stops where the call is out of the money.
--
--   **Formalization Note.** The statement is restricted to $x>0$: at $x=0$ the price is identically $0$ and $V(0,y)=0$, so "strictly positive" holds only on $x>0$.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Remarks 3.3

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Remarks 3.3: the value function is strictly positive,
`V(x, y) > 0`.

**Formalization Note.** Stated for `x > 0`, `y ∈ [0, 1]`: at `x = 0` the asset is identically
`0` and `V(0, y) = 0`, so the page's "strictly positive" holds on `x > 0` only. Model
conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem remark_3_3 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < V p st x y := by sorry

end DynkinIncInfo.Saddle
