-- Prove2me | Theorems.Thm_CalibeatBandit_DrawRun_sampling_conversion
-- name    : CalibeatBandit.DrawRun.sampling_conversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:53:32.175367+00:00
-- url     : https://prove2.me/theorems/d31b3985-2459-4615-8f47-1ab4be531a3e
-- title:
--   §C.1 for a general draw run — $\mathbb E[\mathrm{SR}_T]\le\mathbb E[R^{\mathrm{SR},p}_T]+\sqrt{2TK\log K}$
-- statement:
--   **Sampling conversion (§C.1), for a general draw run.** Let $K\ge1$ and consider a draw run over $T$ rounds: rewards $y_t\in[0,1]^K$ fixed before the draw, and an action $I_t$ drawn from the mixed strategy $p_t$ given everything fixed before the draw. Then
--
--   $$\mathbb E\big[\mathrm{SR}_T\big]\ \le\ \mathbb E\big[R^{\mathrm{SR},p}_T\big]+\sqrt{2TK\log K},$$
--
--   where $\mathrm{SR}_T=\max_\sigma\sum_{t<T}\big(y_t(\sigma(I_t))-y_t(I_t)\big)$ is the swap regret of the sampled actions and $R^{\mathrm{SR},p}_T=\max_\sigma\sum_{t<T}\sum_ip_t(i)\big(y_t(\sigma(i))-y_t(i)\big)$ is the pseudo swap regret of the mixed strategies.
--
--   **Role.** The paper proves this for a run of the interaction protocol (p. 31). The statement here does not mention the learner's algorithm or the recommendation: it uses only that $I_t\sim p_t$ conditionally. It therefore also applies to the pricing algorithm on a price grid (Theorem 5.1) and to the calibeating phase of the robust algorithm (Theorem 3.5).
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Appendix C.1, p. 31 (sampling conversion). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_5_1, where it is stated for a general draw run.

import Definitions.Def_CalibeatBandit_draw_run
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret

set_option autoImplicit false

open CalibeatBandit Matrix Filter MeasureTheory
open scoped BigOperators

theorem CalibeatBandit.DrawRun.sampling_conversion {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) (hK : 0 < K) :
    ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
      ≤ ∫ ω, pseudoSwapRegret T (fun t => run.played t ω) (fun t => run.y t ω) ∂P
        + Real.sqrt (2 * T * K * Real.log K) := by sorry
