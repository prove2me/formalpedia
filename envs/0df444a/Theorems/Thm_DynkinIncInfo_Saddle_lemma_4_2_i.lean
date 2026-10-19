-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_4_2_i
-- name    : DynkinIncInfo.Saddle.lemma_4_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:48.93941+00:00
-- url     : https://prove2.me/theorems/f59beb87-d463-4ca4-aabc-6cb3cd1255e8
-- title:
--   Lemma 4.2 (i), p. 9 — the buyer's stopping region S1 is up-connected in y
-- statement:
--   If $(x,y)\in\mathcal S_1$ and $y\le y'\le1$, then $(x,y')\in\mathcal S_1$.
--
--   A buyer who stops at belief $y$ also stops at any more pessimistic belief about the drift (a larger probability of the dividend).
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 9, Lemma 4.2 (i)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 9, Lemma 4.2 (i): `(x, y) ∈ 𝒮1 ⇒ (x, y') ∈ 𝒮1` for `y' ≥ y`.

**Formalization Note.** `y'` ranges over `[y, 1]` (`𝒮1 ⊆ ℝ₊ × [0, 1]`). Model conventions:
the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_4_2_i {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y y' : ℝ) (hxy : (x, y) ∈ S1 p st) (hyy' : y ≤ y') (hy' : y' ≤ 1) :
    (x, y') ∈ S1 p st := by sorry

end DynkinIncInfo.Saddle
