-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_corollary_5_5_c1
-- name    : DynkinIncInfo.Saddle.corollary_5_5_c1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:50.28977+00:00
-- url     : https://prove2.me/theorems/5d33c9be-af74-4b75-8082-c1f07f983196
-- title:
--   Corollary 5.5 (5.20), p. 15 — c1 is non-decreasing, 0 ≤ c1 ≤ yK, and S'1 = {y ≤ c1(z)}
-- statement:
--   Assume $\sigma^2/\delta_0\ge1$ and $k\neq0$, and let $c_1(z)=\sup\big(\{0\}\cup\{y\in(0,1)\mid(z,y)\in\mathcal S'_1\}\big)$. Then $c_1$ is non-decreasing, $0\le c_1(z)\le1$ and $c_1(z)\le y_K(z)$ for every $z$, and
--   $$\mathcal S'_1=\{(z,y)\in\mathbb R\times(0,1)\mid y\le c_1(z)\}.$$
--
--   The buyer's stopping region in parabolic coordinates lies below the graph of a monotone boundary.
--
--   **Formalization Note.** Only clause (5.20) and the bound $c_1\le y_K$ of Corollary 5.5 are formalized; $c_2$, $z_K$ and (5.21) are not. The corollary asserts the existence of $c_1$; the explicit supremum is used. The page writes $\mathbb R\times[0,1]$ in (5.20), but $\mathcal S'_1\subseteq\mathbb R\times(0,1)$ by definition.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 15, Corollary 5.5, (5.20)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 15, Corollary 5.5, clause (5.20) (under Assumption 5.3, `σ²/δ0 ≥ 1`): the
function `c1 : ℝ → [0, 1]` is non-decreasing, `c1(·) ≤ y_K(·)`, and
`𝒮'1 = {(z, y) | y ≤ c1(z)}`.

**Formalization Note.** `c1` is the explicit `c1(z) = sup({0} ∪ {y ∈ (0, 1) | (z, y) ∈ 𝒮'1})`
(the corollary only asserts existence). The page writes `(z, y) ∈ ℝ × [0, 1]` in (5.20), but
`𝒮'1 ⊆ ℝ × (0, 1)` by definition (p. 13), so `y ∈ (0, 1)` is used. `c1 ≤ y_K` combines the
page's `c1 ≤ c2 ≤ y_K` on `(−∞, z_K]` and `c1 ≤ y_K` on `(z_K, ∞)`; `c2`, `z_K` and (5.21) are
not formalized. `k ≠ 0` is §5's standing assumption (p. 12). Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem corollary_5_5_c1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h53 : 1 ≤ p.σ ^ 2 / p.δ0) (hk : k p ≠ 0) :
    Monotone (c1 p st) ∧
    (∀ z : ℝ, c1 p st z ∈ Set.Icc (0 : ℝ) 1 ∧ c1 p st z ≤ yK p z) ∧
    S1' p st = {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ q.2 ≤ c1 p st q.1} := by sorry

end DynkinIncInfo.Saddle
