-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_eq_5_8
-- name    : ArapostathisAC.RossRecurrence.eq_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:26:22.350304+00:00
-- url     : https://prove2.me/theorems/8f6a7e0a-28b4-4381-b42a-8eac61af91b1
-- title:
--   Display (5.8) — first-return bound J*_β(i) ≤ M E[τ] + J*_β(0) E[β^τ]
-- statement:
--   Consider the countable-state controlled Markov process of §5. Assume the cost is bounded: there is $M$ with $c(i,a)\le M$ for every state $i$ and every $a\in U(i)$, as §5.1 assumes. Let $\beta\in(0,1)$ and let $f_\beta\in\Pi_{SD}$ be $\beta$-discount optimal. Let $\tau=\min\{t\ge1: X_t=0\}$ be the return time to state $0$, with $\beta^\tau=0$ on $\{\tau=\infty\}$. Then for every state $i$,
--   $$J^*_\beta(i)\le M\,E^{f_\beta}_i[\tau]+J^*_\beta(0)\,E^{f_\beta}_i[\beta^\tau].$$
--
--   This is the last line of display (5.8) in the proof of Theorem 5.3. It splits the discounted cost of $f_\beta$ at the first return to $0$: before $\tau$ the cost is at most $M$ per step, and after $\tau$ the process restarts from $0$ under the optimal policy $f_\beta$.
--
--   **Formalization Note.** The paper's intermediate line writes the first sum as $\sum_{t=0}^{\tau-1}\beta^n c(X_t,f_\beta(X_t))$. The exponent should be $t$ (a typo), and only the final inequality is stated here. All quantities are in $[0,\infty]$; $M E^{f_\beta}_i[\tau]$ is $M$ times the mean return time, possibly $+\infty$. The bound on $c$ is the standing hypothesis of §5.1.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 302, proof of Theorem 5.3, (5.8)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Display (5.8) (proof of Theorem 5.3, p. 302): if `c ≤ M₀` on the admissible pairs and
`f ∈ Π_SD` is `β`-discount optimal, then `J*_β(i) ≤ M₀ E^f_i[τ] + J*_β(0) E^f_i[β^τ]`. -/
theorem eq_5_8 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : StationaryPolicy M) (hf : IsDiscOptimal M f β)
    (i : ℕ) :
    discValue M β i ≤
      ENNReal.ofReal M₀ * meanReturnTime M f i + discValue M β 0 * expDiscAtReturn M f β i := by sorry

end ArapostathisAC.RossRecurrence
