-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_sub
-- name    : DynkinIncInfo.Saddle.theorem_3_2_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:08.046567+00:00
-- url     : https://prove2.me/theorems/1a99aca3-030e-450d-b7f8-820bc1c69004
-- title:
--   Theorem 3.2 (3.7), p. 8 — e^{−r(t∧τ*)}V(X_{t∧τ*}, Y_{t∧τ*}) is a submartingale
-- statement:
--   Let $x\ge0$, $y\in[0,1]$ and let $\tau_*=\inf\{t\ge0\mid V(X_t,Y_t)\le G_1(X_t)\}$ (with $\inf\emptyset=+\infty$) be the buyer's entry time into the buyer's stopping region. The stopped discounted value process
--   $$t\mapsto e^{-r(t\wedge\tau_*)}\,V\big(X_{t\wedge\tau_*},Y_{t\wedge\tau_*}\big),\qquad t\ge0,$$
--   is an $\overline{\mathcal F}^S$-submartingale (not necessarily closed), and $\tau_*$ is an $\overline{\mathcal F}^S$-stopping time.
--
--   This is the property that the proof of Proposition 7.3 combines with optional sampling.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2, (3.7)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2 (submartingale): for `(x, y) ∈ ℝ₊ × [0, 1]`, with
`τ*(x, y) = inf{t ≥ 0 | V(X_t, Y_t) ≤ G1(X_t)}` ((3.7), `inf ∅ = +∞`), the process
`τ*` is an `𝓕̄^S`-stopping time and
`e^{−r(t∧τ*)} V(X_{t∧τ*}, Y_{t∧τ*})`, `t ≥ 0`, is an `𝓕̄^S`-submartingale.

**Formalization Note.** Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem theorem_3_2_sub {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    IsST p st x y (τstar p st x y) ∧
    Submartingale (stoppedProcess (discV p st x y) (τstar p st x y))
      (FS p st x y) st.P := by sorry

end DynkinIncInfo.Saddle
