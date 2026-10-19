-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_value
-- name    : DynkinIncInfo.Saddle.theorem_3_2_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:08.437242+00:00
-- url     : https://prove2.me/theorems/fd37d3ce-7fdf-4231-bb8a-d506cfcd2c97
-- title:
--   Theorem 3.2, p. 8 — the game has a value: V̲ = V̄ on ℝ₊ × [0, 1]
-- statement:
--   For every initial price $x\ge0$ and prior $y\in[0,1]$, the lower and upper values of the game coincide:
--   $$\underline V(x,y)=\overline V(x,y).$$
--
--   This is the existence-of-value part of Theorem 3.2. It is nontrivial because the payoff processes are not uniformly integrable and the price alone is not Markov.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2 (value): the game has a value,
`V̲(x, y) = V̄(x, y)` for all `(x, y) ∈ ℝ₊ × [0, 1]`.

**Formalization Note.** Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem theorem_3_2_value {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Vlow p st x y = Vup p st x y := by sorry

end DynkinIncInfo.Saddle
