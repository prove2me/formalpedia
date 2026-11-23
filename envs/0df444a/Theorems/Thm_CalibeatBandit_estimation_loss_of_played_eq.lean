-- Prove2me | Theorems.Thm_CalibeatBandit_estimation_loss_of_played_eq
-- name    : CalibeatBandit.estimation_loss_of_played_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:55:48.173955+00:00
-- url     : https://prove2.me/theorems/1704410d-e74f-4378-8fb9-97ca660b373e
-- title:
--   Lemma C.4 for a general draw run — estimation loss at most $|\iota|\log K/\eta$
-- statement:
--   **Lemma C.4 (estimation loss), for a general draw run.** Let $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $4K\eta\le\mu$. Consider a draw run over $T$ rounds in which the mixed strategy is $p_t=(1-\mu)x_t+\mu/K$ for probability vectors $x_t$ measurable with respect to the information before the draw, with corrected reward estimates $v_t(j)=\frac{y_t(I_t)\mathbf 1[I_t=j]}{p_t(j)}+\frac{(e-2)\eta}{p_t(j)}$. Let $\iota$ be a finite index set and $w_t$ probability vectors on $\iota$, measurable with respect to the information before the draw. Then
--
--   $$\mathbb E\Big[\max_{f:\iota\to[K]}\sum_{t<T}\sum_{i\in\iota}w_t(i)\big(y_t(f(i))-v_t(f(i))\big)\Big]\ \le\ \frac{|\iota|\,\log K}{\eta}.$$
--
--   **Role.** The lemma says that replacing the true rewards by the corrected estimates cannot help a comparator that assigns one action to each index, up to $|\iota|\log K/\eta$. With $\iota=[K]$ and $w_t=x_t$ it is the swap-regret half of Lemma C.4 of the paper, and with $w_t$ the indicator of the recommended action it is the other half. With a general index set it also covers the pricing algorithm, where the recommendation takes values in a set of prices different from the grid.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Appendix C.2, Lemma C.4, p. 35. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_5_1, where it is stated for a general draw run.

import Definitions.Def_CalibeatBandit_draw_run
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret

set_option autoImplicit false

open CalibeatBandit Matrix Filter MeasureTheory
open scoped BigOperators

theorem CalibeatBandit.estimation_loss_of_played_eq {K T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hne : (Finset.univ : Finset (ι → Fin K)).Nonempty)
    {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω))
    (w : ℕ → Ω → ι → ℝ) (hw₀ : ∀ t < T, ∀ ω i, 0 ≤ w t ω i)
    (hw : ∀ t < T, ∀ ω, ∑ i, w t ω i = 1)
    (hwm : ∀ t < T, Measurable[run.preDraw t] (w t)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, Finset.univ.sup' hne (fun f : ι → Fin K =>
      ∑ t ∈ Finset.range T, ∑ i, w t ω i * (run.y t ω (f i) - v t ω (f i))) ∂P
      ≤ Fintype.card ι * Real.log K / η := by sorry
