-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_4_2_iii
-- name    : DynkinIncInfo.Saddle.lemma_4_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:56.680979+00:00
-- url     : https://prove2.me/theorems/b61890da-40f6-4fde-9970-762e3466d37f
-- title:
--   Lemma 4.2 (iii), p. 10 — S1 is right-connected in x ≥ K
-- statement:
--   If $(x,y)\in\mathcal S_1$ and $x'\ge x\ge K$, then $(x',y)\in\mathcal S_1$.
--
--   Together with Lemma 4.2 (i) this shows that the buyer's stopping region lies above a non-increasing boundary.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 10, Lemma 4.2 (iii)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 10, Lemma 4.2 (iii): `(x, y) ∈ 𝒮1 ⇒ (x', y) ∈ 𝒮1` for `x' ≥ x ≥ K`.

**Formalization Note.** Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_4_2_iii {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x x' y : ℝ) (hxy : (x, y) ∈ S1 p st) (hKx : p.K ≤ x) (hxx' : x ≤ x') :
    (x', y) ∈ S1 p st := by sorry

end DynkinIncInfo.Saddle
