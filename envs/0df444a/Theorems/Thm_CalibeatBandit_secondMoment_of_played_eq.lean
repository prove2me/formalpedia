-- Prove2me | Theorems.Thm_CalibeatBandit_secondMoment_of_played_eq
-- name    : CalibeatBandit.secondMoment_of_played_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:54:12.192143+00:00
-- url     : https://prove2.me/theorems/22495d19-d5b6-49f6-81e5-e427f43f357d
-- title:
--   Eq. (C.6) for a general draw run — $\mathbb E[\sum_jx(j)v(j)^2\mid\mathcal G_t]\le2K/(1-\mu)$
-- statement:
--   **Equation (C.6), for a general draw run.** Let $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $4K\eta\le\mu$. Consider a draw run and a round $t<T$ in which the mixed strategy is $p=(1-\mu)x+\mu/K$ for a probability vector $x$ that is measurable with respect to the information before the draw. Let
--
--   $$v(j)=\frac{y_t(I_t)\,\mathbf 1[I_t=j]}{p(j)}+\frac{(e-2)\eta}{p(j)}$$
--
--   be the corrected reward estimate. Then, almost surely,
--
--   $$\mathbb E\Big[\sum_jx(j)\,v(j)^2\,\Big|\,\mathcal G_t\Big]=\sum_j\frac{x(j)}{p(j)}\Big(y_t(j)^2+2(e-2)\eta\,y_t(j)+\frac{(e-2)^2\eta^2}{p(j)}\Big),$$
--
--   and the right-hand side is at most $2\sum_jx(j)/p(j)\le\frac{2K}{1-\mu}$ at every point.
--
--   **Role.** This is the second-moment bound (C.6) used in Lemma C.3. The paper proves it for the bandit calibeating algorithm; here the hypothesis is only that the action is drawn from $(1-\mu)x+\mu/K$, so the bound is available for every algorithm that explores uniformly with probability $\mu$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Appendix C.2, proof of Lemma C.3, equation (C.6), p. 34. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_5_1, where it is stated for a general draw run.

import Definitions.Def_CalibeatBandit_draw_run
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret

set_option autoImplicit false

open CalibeatBandit Matrix Filter MeasureTheory
open scoped BigOperators

theorem CalibeatBandit.secondMoment_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : DrawRun K T P) (t : ℕ) (ht : t < T)
    (x : Ω → Fin K → ℝ) (hx : ∀ ω, IsProbVec (x ω)) (hxm : Measurable[run.preDraw t] x)
    (hplay : run.played t =ᵐ[P] fun ω => explore μ (x ω)) :
    let v := fun ω => estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω)
    let p := fun ω => explore μ (x ω)
    condExp (run.preDraw t) P (fun ω => ∑ j, x ω j * v ω j ^ 2)
      =ᵐ[P] (fun ω => ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j)) ∧
    (∀ ω, ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j) ≤ 2 * ∑ j, x ω j / p ω j) ∧
    (∀ ω, 2 * ∑ j, x ω j / p ω j ≤ 2 * K / (1 - μ)) := by sorry
