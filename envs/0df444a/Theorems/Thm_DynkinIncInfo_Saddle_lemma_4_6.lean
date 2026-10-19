-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_4_6
-- name    : DynkinIncInfo.Saddle.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:01.551874+00:00
-- url     : https://prove2.me/theorems/d21425fc-f5c9-4cd7-b565-9e679333f07c
-- title:
--   Lemma 4.6, p. 11 — b1(y) < ∞ for every y ∈ (0, 1)
-- statement:
--   For every $y\in(0,1)$,
--   $$b_1(y)<\infty,$$
--   that is, at every interior belief the buyer's stopping region is nonempty.
--
--   This finiteness is what bounds the price before the buyer stops in the proof of Proposition 7.3.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 11, Lemma 4.6

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 11, Lemma 4.6: for all `y ∈ (0, 1)`, `b1(y) < ∞`.

**Formalization Note.** `b1` is valued in `ℝ≥0∞` with `inf ∅ = +∞`. Model conventions:
the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    b1 p st y < ⊤ := by sorry

end DynkinIncInfo.Saddle
