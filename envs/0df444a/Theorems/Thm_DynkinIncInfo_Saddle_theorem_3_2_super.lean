-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_theorem_3_2_super
-- name    : DynkinIncInfo.Saddle.theorem_3_2_super
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:58.981572+00:00
-- url     : https://prove2.me/theorems/397378b4-630a-4a31-a72f-34f6bfdada53
-- title:
--   Theorem 3.2, p. 8 — e^{−r(t∧γ*)}V(X_{t∧γ*}, Y_{t∧γ*}) is a closed supermartingale
-- statement:
--   Let $x\ge0$, $y\in[0,1]$ and $\gamma_*$ the seller's entry time. The stopped discounted value process
--   $$t\mapsto e^{-r(t\wedge\gamma_*)}\,V\big(X_{t\wedge\gamma_*},Y_{t\wedge\gamma_*}\big),\qquad t\ge0,$$
--   is an $\overline{\mathcal F}^S$-supermartingale, and it is closed:
--   $$\mathbb E\big[e^{-r\gamma_*}V(X_{\gamma_*},Y_{\gamma_*})\mathbf 1_{\{\gamma_*<\infty\}}\big]\le V(x,y).$$
--
--   This is the martingale characterisation of the seller's optimality.
--
--   **Formalization Note.** "Closed" (a supermartingale with a last element, p. 32) is stated as the displayed inequality, with integrand $0$ on $\{\gamma_*=\infty\}$, where the process tends to $0$ by (3.1). The expectation is a Lebesgue integral of a nonnegative function.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 8, Theorem 3.2 (closed supermartingale): for `(x, y) ∈ ℝ₊ × [0, 1]`,
the process `e^{−r(t∧γ*)} V(X_{t∧γ*}, Y_{t∧γ*})`, `t ≥ 0`, is an `𝓕̄^S`-supermartingale, and it
is closed: `E[e^{−rγ*} V(X_{γ*}, Y_{γ*}) 1{γ* < ∞}] ≤ V(x, y)`.

**Formalization Note.** "Closed" (a supermartingale with a last element, p. 32) is stated as the
displayed inequality, with the integrand `0` on `{γ* = ∞}` (the limit of the process there,
by (3.1)); the expectation is a `lintegral`. Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem theorem_3_2_super {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Supermartingale (stoppedProcess (discV p st x y) (γstar p st x y)) (FS p st x y) st.P ∧
      ∫⁻ ω, (if γstar p st x y ω = ⊤ then 0 else
          ENNReal.ofReal (Real.exp (-p.r * ((γstar p st x y ω).untopA : ℝ)) *
            V p st (S p st x y (γstar p st x y ω).untopA ω)
              (Y p st x y (γstar p st x y ω).untopA ω))) ∂st.P
        ≤ ENNReal.ofReal (V p st x y) := by sorry

end DynkinIncInfo.Saddle
