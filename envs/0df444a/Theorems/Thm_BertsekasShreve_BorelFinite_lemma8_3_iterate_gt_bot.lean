-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_3_iterate_gt_bot
-- name    : BertsekasShreve.BorelFinite.lemma8_3_iterate_gt_bot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:17:46.855255+00:00
-- url     : https://prove2.me/theorems/a8831ea2-28ea-4e70-b2f4-2b03db007db5
-- title:
--   Lemma 8.3 — under (F⁺) the iterates T^K(J₀) never take the value −∞
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺). If $J_0:S\to R^*$ is identically zero, then
--   $$T^K(J_0)(x)>-\infty\qquad\text{for every }x\in S,\ K=1,\dots,N,$$
--   where $T^K$ denotes the composition of $T$ with itself $K$ times.
--
--   This finiteness from below is what allows $\varepsilon$-optimal selectors to be accumulated along the dynamic programming recursion under (F⁺).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 196, Lemma 8.3

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **Lemma 8.3** (p. 196). Under (F⁺), with `J₀ ≡ 0`, `T^K(J₀)(x) > -∞` for every `x ∈ S` and
`K = 1, …, N`. -/
theorem lemma8_3_iterate_gt_bot {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) (x : S) :
    ⊥ < (T M)^[K] (J0 S) x := by sorry

end BertsekasShreve.BorelFinite
