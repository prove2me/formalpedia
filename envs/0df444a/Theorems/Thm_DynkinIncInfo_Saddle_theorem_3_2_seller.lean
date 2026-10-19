-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_seller
-- name    : DynkinIncInfo.Saddle.theorem_3_2_seller
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:06.309431+00:00
-- url     : https://prove2.me/theorems/fb8b0018-ba52-4727-bc58-1ff5f18ab000
-- title:
--   Theorem 3.2 (3.6), p. 8 — γ* is a stopping time and optimal for the seller: V̄ = sup_τ M(τ, γ*)
-- statement:
--   Let $x\ge0$, $y\in[0,1]$, and let $\gamma_*=\inf\{t\ge0\mid G_2(X_t)\le V(X_t,Y_t)\}$ (with $\inf\emptyset=+\infty$) be the first time the observed state enters the seller's stopping region. Then $\gamma_*$ is an $\overline{\mathcal F}^S$-stopping time and
--   $$\overline V(x,y)=\sup_{\tau}M_{x,y}(\tau,\gamma_*),$$
--   the supremum being over all $\overline{\mathcal F}^S$-stopping times.
--
--   So the seller has an optimal strategy: cancelling at $\gamma_*$ guarantees that the buyer cannot obtain more than the value.
--
--   **Formalization Note.** "Player 2 has an optimal strategy $\gamma_*$" is stated in the form proved in Appendix A (p. 32).
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2, (3.6)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2 (optimal strategy of the seller): the entry time
`γ*(x, y) = inf{t ≥ 0 | G2(X_t) ≤ V(X_t, Y_t)}` ((3.6), `inf ∅ = +∞`) is an `𝓕̄^S`-stopping time
and is optimal for player 2: `V̄(x, y) = sup_τ M_{x,y}(τ, γ*)`, for `(x, y) ∈ ℝ₊ × [0, 1]`.

**Formalization Note.** "Player 2 has an optimal strategy `γ*`" is stated as
`V̄(x, y) = sup_τ M(τ, γ*)`, the form proved in Appendix A (p. 32). Model conventions:
the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem theorem_3_2_seller {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    IsST p st x y (γstar p st x y) ∧
      Vup p st x y = ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsST p st x y τ),
        M p st x y τ (γstar p st x y) := by sorry

end DynkinIncInfo.Saddle
