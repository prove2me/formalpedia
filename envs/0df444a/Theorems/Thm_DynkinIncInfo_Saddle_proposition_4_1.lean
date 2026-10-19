-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_proposition_4_1
-- name    : DynkinIncInfo.Saddle.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:10.13654+00:00
-- url     : https://prove2.me/theorems/7ee1e1c1-a94a-4767-ba0d-7a054a4c8550
-- title:
--   Proposition 4.1, p. 9 — S1 ⊆ A1ᶜ ∩ {x > K} and S2 ∩ {x > K} ⊆ A2ᶜ
-- statement:
--   Let $A_1=\{(x,y)\mid xy<rK/\delta_0,\ x>K\}$ and $A_2=\{(x,y)\mid xy>r(K-\varepsilon_0)/\delta_0,\ x>K\}$, with $y\in[0,1]$, and let $\{x>K\}=(K,\infty)\times[0,1]$. Then
--   $$\mathcal S_1\subseteq A_1^c\cap\{x>K\}\qquad\text{and}\qquad \mathcal S_2\cap\{x>K\}\subseteq A_2^c,$$
--   the complements being taken in $\mathbb R_+\times[0,1]$ with $\mathbb R_+=(0,\infty)$.
--
--   So the buyer never stops out of the money or where the generator of the discounted exercise payoff is positive, and symmetrically for the seller.
--
--   **Formalization Note.** The degenerate price $x=0$ (where $V(0,y)=0=G_1(0)$) is excluded from $\mathcal S_1,\mathcal S_2$; with it the first inclusion would fail. $A_1$, $A_2$ are taken in the explicit form printed on p. 9 instead of through the generator (4.5).
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 9, Proposition 4.1 (with (4.6)–(4.7) and the explicit A1, A2 on the same page)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 9, Proposition 4.1: `𝒮1 ⊆ A1ᶜ ∩ {x > K}` and `𝒮2 ∩ {x > K} ⊆ A2ᶜ`, where
`A1 = {(x, y) | xy < rK/δ0 and x > K}`, `A2 = {(x, y) | xy > r(K − ε0)/δ0 and x > K}`
(p. 9, the explicit forms of (4.6)–(4.7)) and `{x > K} = (K, +∞) × [0, 1]`.

**Formalization Note.** `A1`, `A2` are taken in the explicit form printed on p. 9, so no
generator is defined; the complements are taken in `ℝ₊ × [0, 1]`, which contains `𝒮1`, `𝒮2`. Here `ℝ₊ = (0, ∞)`: at the
degenerate state `x = 0` the price is identically `0` and `V(0, y) = 0 = G1(0)`, so `x = 0` is
excluded from the regions (otherwise `(0, y) ∈ 𝒮1` would contradict `𝒮1 ⊆ {x > K}`).
Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω) :
    (∀ q ∈ S1 p st, q ∉ A1 p ∧ p.K < q.1) ∧
    (∀ q ∈ S2 p st, p.K < q.1 → q ∉ A2 p) := by sorry

end DynkinIncInfo.Saddle
