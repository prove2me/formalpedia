-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_proposition_7_3
-- name    : DynkinIncInfo.Saddle.proposition_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:04.69845+00:00
-- url     : https://prove2.me/theorems/9eaa5f04-6633-4910-9e53-211b179473b2
-- title:
--   Proposition 7.3, p. 26 — if k > 0 (and σ²/δ0 > 1), the entry times (γ*, τ*) of Theorem 3.2 form a saddle point of the game
-- statement:
--   Consider the game call option on the asset $S^x_t=x\exp(\sigma B_t+(r-\delta_0D)t-t\sigma^2/2)$, where the dividend indicator $D$ is unobservable with $\mathbb P(D=1)=y$ and both players use stopping times of the price filtration $\overline{\mathcal F}^S$. Assume $\sigma^2/\delta_0>1$ (Assumption 7.1) and
--   $$k=r-\frac{\sigma^2}{2}-\frac{\delta_0}{2}>0.$$
--   Then for every $x>0$ and $y\in(0,1)$ the entry times
--   $$\tau_*=\inf\{t\ge0\mid V(X_t,Y_t)\le G_1(X_t)\},\qquad \gamma_*=\inf\{t\ge0\mid G_2(X_t)\le V(X_t,Y_t)\}$$
--   are stopping times and form a saddle point:
--   $$M_{x,y}(\tau,\gamma_*)\le M_{x,y}(\tau_*,\gamma_*)\le M_{x,y}(\tau_*,\gamma)\qquad\text{for all stopping times }\tau,\gamma.$$
--
--   Hence the game has a Nash equilibrium in pure strategies, in which each player stops when the observed state $(X_t,Y_t)$ (price and posterior belief) enters their own stopping region.
--
--   **Formalization Note.** The statement is restricted to $x>0$, $y\in(0,1)$: at $y=0$ the pair is not a saddle point (Proposition C.1, p. 36). $X:=S$ and $Y$ is the closed-form Bayes filter on the original space (same law as the paper's SDE solution, p. 6). $M$ is a Lebesgue integral with payoff $0$ on $\{\tau\wedge\gamma=\infty\}$, stopping times take values in $[0,\infty]$, and $V=\overline V$ is the game's own value, so $\tau_*,\gamma_*$ are determined by the model.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 26, Proposition 7.3 (with Assumption 7.1, p. 25, and the saddle-point definition, p. 3)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the
Return, arXiv:1705.07352v4, p. 26, Proposition 7.3 (under the standing Assumption 7.1,
`σ²/δ0 > 1`, p. 25): if `k = r − σ²/2 − δ0/2 > 0`, the pair `(γ*, τ*)` defined in Theorem 3.2 is a
saddle point: both are `𝓕̄^S`-stopping times and
`M_{x,y}(τ, γ*) ≤ M_{x,y}(τ*, γ*) ≤ M_{x,y}(τ*, γ)` for all `𝓕̄^S`-stopping times `τ`, `γ`.

Here `γ* = inf{t ≥ 0 | G2(X_t) ≤ V(X_t, Y_t)}` and `τ* = inf{t ≥ 0 | V(X_t, Y_t) ≤ G1(X_t)}`
((3.6)–(3.7), `inf ∅ = +∞`) are the entry times of the observed state into the seller's and the
buyer's stopping regions, and `V` is the value of the game.

**Formalization Note.** The statement is posed for `x > 0` and `y ∈ (0, 1)`: at `y = 0` the pair is
not a saddle point (Proposition C.1, p. 36), and the proof sets `x = F(z, y)`, which needs
`y ∈ (0, 1)`. The paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original
space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6);
`D^y = 1{U < y}` with `U` uniform and independent of `B`. Stopping times are `𝓕̄^S`-stopping times
(the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with
payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`, and `τ*`, `γ*` are built from this `V`. The pair is
written `(τ*, γ*)` in the order of the definition on p. 3 (buyer first). -/
theorem proposition_7_3 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h71 : 1 < p.σ ^ 2 / p.δ0) (hk : 0 < k p)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    IsSaddle p st x y (τstar p st x y) (γstar p st x y) := by sorry

end DynkinIncInfo.Saddle
