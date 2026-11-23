-- Prove2me | Theorems.Thm_CalibeatBandit_correction_loss_of_played_eq
-- name    : CalibeatBandit.correction_loss_of_played_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:54:46.346007+00:00
-- url     : https://prove2.me/theorems/07a502c4-d345-4b3d-92bb-f3c295ed922d
-- title:
--   Lemma C.5 for a general draw run — correction loss at most $(e-2)\eta KT/(1-\mu)$
-- statement:
--   **Lemma C.5 (correction loss), for a general draw run.** Let $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $4K\eta\le\mu$. Consider a draw run over $T$ rounds in which, in every round, the mixed strategy is $p_t=(1-\mu)x_t+\mu/K$ for probability vectors $x_t$ measurable with respect to the information before the draw, and let $v_t(j)=\frac{y_t(I_t)\mathbf 1[I_t=j]}{p_t(j)}+\frac{(e-2)\eta}{p_t(j)}$ be the corrected reward estimates. Then
--
--   $$\mathbb E\Big[\sum_{t<T}\langle x_t,\,v_t-y_t\rangle\Big]\ \le\ \frac{(e-2)\,\eta KT}{1-\mu}.$$
--
--   **Role.** The estimate $v_t$ overestimates $y_t$ on average by the correction term $(e-2)\eta/p_t(j)$; the lemma bounds the total cost of this correction. The paper states it for the bandit calibeating algorithm (Lemma C.5); here only the form of the mixed strategy is assumed.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Appendix C.2, Lemma C.5, p. 36. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_5_1, where it is stated for a general draw run.

import Definitions.Def_CalibeatBandit_draw_run
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret

set_option autoImplicit false

open CalibeatBandit Matrix Filter MeasureTheory
open scoped BigOperators

theorem CalibeatBandit.correction_loss_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (_hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, ∑ t ∈ Finset.range T, x t ω ⬝ᵥ (v t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) := by sorry
