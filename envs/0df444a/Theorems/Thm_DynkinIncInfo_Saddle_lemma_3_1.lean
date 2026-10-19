-- Prove2me | Theorems.Thm_DynkinIncInfo_Saddle_lemma_3_1
-- name    : DynkinIncInfo.Saddle.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:18.472579+00:00
-- url     : https://prove2.me/theorems/603ce276-6cf2-4851-bbb1-dbdc48431f93
-- title:
--   Lemma 3.1, p. 6 — V̄ and V̲ are monotone, 1-Lipschitz in x, and C(1+|x|)-Lipschitz in y
-- statement:
--   Let $f$ be either the lower value $\underline V$ or the upper value $\overline V$ of the game (both finite). Then:
--
--   1. $f$ is non-decreasing in $x\ge0$ and non-increasing in $y\in[0,1]$;
--   2. $f$ is $1$-Lipschitz in $x$, uniformly in $y$: $|f(x,y)-f(x',y)|\le|x-x'|$ for $x,x'\ge0$, $y\in[0,1]$;
--   3. there is a constant $C>0$ such that
--   $$|f(x,y)-f(x,y')|\le C(1+|x|)\,|y-y'|\qquad\text{for all }x>0,\ y,y'\in[0,1].$$
--
--   These regularity properties give continuity of the value, hence closedness of the stopping regions, and are used throughout §4–§5.
--
--   **Formalization Note.** The page's "a given constant $C>0$" is read as the existence of one constant $C$ for all $x,y,y'$.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 6, Lemma 3.1

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

/-- De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, p. 6, Lemma 3.1: the functions `V̄` and `V̲` are
(i) non-decreasing in `x` and non-increasing in `y`; (ii) 1-Lipschitz in `x`, uniformly in
`y ∈ [0, 1]`; (iii) locally Lipschitz in `y`: `|f(x, y) − f(x, y')| ≤ C(1 + |x|)|y − y'|` for
`x > 0`, `y, y' ∈ [0, 1]`.

**Formalization Note.** Stated for `f = V̲.toReal` and `f = V̄.toReal` (both are finite,
`V̲ ≤ V̄ ≤ G2(x)`). (i) and (ii) are stated for `x, x' ≥ 0`. In (iii) the page's "a given
constant `C > 0`" is read as "there is a constant `C > 0`" (independent of `x, y, y'`).
Model conventions: the paper's `(X, Y)` (solution of the SDE (2.3)) is represented on the original space of §2 by `X := S` (2.1) and the closed-form Bayes filter `Y`, which have the same law (p. 6); `D^y = 1{U < y}` with `U` uniform and independent of `B`; stopping times are `𝓕̄^S`-stopping times (the filtration of `S` augmented by the null sets) valued in `[0, ∞]`; `M` is a `lintegral` with payoff `0` on `{τ ∧ γ = ∞}`; `V := V̄.toReal`. -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (f : ℝ → ℝ → ℝ)
    (hf : f = (fun x y => (Vlow p st x y).toReal) ∨ f = (fun x y => (Vup p st x y).toReal)) :
    (∀ x x' y : ℝ, 0 ≤ x → x ≤ x' → y ∈ Set.Icc (0 : ℝ) 1 → f x y ≤ f x' y) ∧
    (∀ x y y' : ℝ, 0 ≤ x → y ∈ Set.Icc (0 : ℝ) 1 → y' ∈ Set.Icc (0 : ℝ) 1 → y ≤ y' →
      f x y' ≤ f x y) ∧
    (∀ x x' y : ℝ, 0 ≤ x → 0 ≤ x' → y ∈ Set.Icc (0 : ℝ) 1 → |f x y - f x' y| ≤ |x - x'|) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x y y' : ℝ, 0 < x → y ∈ Set.Icc (0 : ℝ) 1 → y' ∈ Set.Icc (0 : ℝ) 1 →
      |f x y - f x y'| ≤ C * (1 + |x|) * |y - y'|) := by sorry

end DynkinIncInfo.Saddle
