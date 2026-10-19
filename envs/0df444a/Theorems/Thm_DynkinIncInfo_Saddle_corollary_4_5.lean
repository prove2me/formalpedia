-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_corollary_4_5
-- name    : DynkinIncInfo.Saddle.corollary_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:06.458824+00:00
-- url     : https://prove2.me/theorems/4b6849e3-262b-4ea9-93f5-02fc0fbcf081
-- title:
--   Corollary 4.5, p. 11 — b1, b2 non-increasing, S1 = {x ≥ b1(y)}, S2 = {K ≤ x ≤ b2(y)}, b1 l.s.c., b2 u.s.c., b1 ≥ b2
-- statement:
--   Let $b_1(y)=\inf\{x>0\mid V(x,y)=G_1(x)\}$ and $b_2(y)=\sup\{x>0\mid V(x,y)=G_2(x)\}$, with $\inf\emptyset=+\infty$ and $\sup\emptyset=0$. Then:
--
--   1. $b_1$ and $b_2$ are non-increasing on $[0,1]$;
--   2. the stopping sets are
--   $$\mathcal S_1=\{(x,y)\in\mathbb R_+\times[0,1]: x\ge b_1(y)\},\qquad \mathcal S_2=\{(x,y)\in\mathbb R_+\times[0,1]: K\le x\le b_2(y)\};$$
--   3. $b_1$ is lower semicontinuous and $b_2$ is upper semicontinuous on $[0,1]$;
--   4. $b_1\ge b_2$ on $[0,1]$.
--
--   The stopping regions are thus described by two monotone free boundaries.
--
--   **Formalization Note.** $\mathbb R_+=(0,\infty)$: the page writes $x\in[0,\infty)$ in (4.11)–(4.12), but at $x=0$ the price stays $0$ and $V(0,y)=0=G_1(0)$, which would make $b_1\equiv0$; that state is excluded. $b_1,b_2$ take values in $[0,\infty]$ and are compared with $x$ there. The page's parenthetical consequences "(hence right-continuous)" and "(hence left-continuous)" are not stated.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 11, Corollary 4.5 (with (4.11)–(4.12))

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game
import Definitions.Def_DynkinIncInfo_Saddle_Regions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 11, Corollary 4.5: the boundaries
`b1(y) = inf{x ∈ [0, ∞) | V(x, y) = G1(x)}` and `b2(y) = sup{x ∈ [0, ∞) | V(x, y) = G2(x)}`
((4.11)–(4.12), `inf ∅ = +∞`, `sup ∅ = 0`) are non-increasing on `[0, 1]` and
`𝒮1 = {(x, y) ∈ ℝ₊ × [0, 1] : x ≥ b1(y)}`, `𝒮2 = {(x, y) ∈ ℝ₊ × [0, 1] : K ≤ x ≤ b2(y)}`;
`b1` is lower semicontinuous, `b2` is upper semicontinuous, and `b1 ≥ b2` on `[0, 1]`.

**Formalization Note.** `ℝ₊ = (0, ∞)`: the degenerate state `x = 0`, where `V(0, y) = 0 = G1(0)`,
is excluded from `𝒮1`, `𝒮2` and from the sets defining `b1`, `b2` (with it, `b1 ≡ 0`). `b1`, `b2`
take values in `[0, ∞]` (`ℝ≥0∞`) and the comparisons with `x` are made in `ℝ≥0∞`. The parenthetical consequences "(hence right-continuous)" and
"(hence left-continuous)" are not stated. Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem corollary_4_5 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω) :
    AntitoneOn (b1 p st) (Set.Icc 0 1) ∧ AntitoneOn (b2 p st) (Set.Icc 0 1) ∧
    S1 p st = {q | q ∈ dom ∧ b1 p st q.2 ≤ ENNReal.ofReal q.1} ∧
    S2 p st = {q | q ∈ dom ∧ p.K ≤ q.1 ∧ ENNReal.ofReal q.1 ≤ b2 p st q.2} ∧
    LowerSemicontinuousOn (b1 p st) (Set.Icc 0 1) ∧
    UpperSemicontinuousOn (b2 p st) (Set.Icc 0 1) ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1, b2 p st y ≤ b1 p st y := by sorry

end DynkinIncInfo.Saddle
