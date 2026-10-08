-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_eq_5_9
-- name    : ArapostathisAC.RossRecurrence.eq_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:26:33.261377+00:00
-- url     : https://prove2.me/theorems/8d3d78b8-b5e1-4e9c-9e11-19da2be482a3
-- title:
--   Display (5.9) — J*_β(i) − β J*_β(0) ≤ MK
-- statement:
--   Consider the countable-state controlled Markov process of §5 with bounded cost, $c(i,a)\le M$ for every $i$ and $a\in U(i)$. Let $\tau=\min\{t\ge1:X_t=0\}$ and assume Ross's recurrence condition (5.7): there is $K>0$ with
--   $$E^f_i[\tau]<K\qquad\text{for all } f\in\Pi_{SD},\ i\in S.$$
--   Then for every $\beta\in(0,1)$ and every state $i$,
--   $$J^*_\beta(i)-\beta J^*_\beta(0)\le MK.$$
--
--   This is the upper half of the uniform bound on $h_\beta$ in Theorem 5.3.
--
--   **Formalization Note.** Under bounded cost, $J^*_\beta$ is finite, so its value is used as a real number.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 302, proof of Theorem 5.3, (5.9)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Display (5.9) (proof of Theorem 5.3, p. 302): if `c ≤ M₀` on the admissible pairs and the mean
return time to `0` is below `K` under every `f ∈ Π_SD` from every state (5.7), then
`J*_β(i) − β J*_β(0) ≤ M₀ K` for every `β ∈ (0, 1)` and every state `i`. -/
theorem eq_5_9 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    (discValue M β i).toReal - β * (discValue M β 0).toReal ≤ M₀ * K := by sorry

end ArapostathisAC.RossRecurrence
