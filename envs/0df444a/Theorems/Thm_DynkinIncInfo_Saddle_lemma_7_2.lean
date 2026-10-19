-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_7_2
-- name    : DynkinIncInfo.Saddle.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:06.414988+00:00
-- url     : https://prove2.me/theorems/2982393a-d408-44d9-a6ce-022331874e7f
-- title:
--   Lemma 7.2, p. 25 — under σ²/δ0 > 1, c1(z) > 0 for every z ∈ ℝ
-- statement:
--   Assume $\sigma^2/\delta_0>1$ (Assumption 7.1) and $k\neq0$. For every $z\in\mathbb R$,
--   $$c_1(z)>0.$$
--
--   In the proof of Proposition 7.3 this keeps the belief bounded away from $0$ before the buyer stops, which bounds the price and circumvents the lack of uniform integrability.
--
--   **Formalization Note.** $c_1(z)=\sup(\{0\}\cup\{y\in(0,1)\mid(z,y)\in\mathcal S'_1\})$. $k\neq0$ is the standing assumption of §5.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 25, Lemma 7.2 (with Assumption 7.1)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 25, Lemma 7.2 (under Assumption 7.1, `σ²/δ0 > 1`): for every `z ∈ ℝ`,
`c1(z) > 0`.

**Formalization Note.** `c1(z) = sup({0} ∪ {y ∈ (0, 1) | (z, y) ∈ 𝒮'1})` (Corollary 5.5).
`k ≠ 0` is §5's standing assumption (p. 12). Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_7_2 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h71 : 1 < p.σ ^ 2 / p.δ0) (hk : k p ≠ 0) (z : ℝ) :
    0 < c1 p st z := by sorry

end DynkinIncInfo.Saddle
