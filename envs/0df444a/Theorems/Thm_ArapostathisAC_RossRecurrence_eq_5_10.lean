-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_eq_5_10
-- name    : ArapostathisAC.RossRecurrence.eq_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:26:52.480692+00:00
-- url     : https://prove2.me/theorems/d7104840-7358-4733-a29b-05700054ca56
-- title:
--   Display (5.10) — J*_β(0) − J*_β(i) ≤ (1 − β^K) J*_β(0) ≤ (1 − β^K) M/(1 − β) ≤ MK
-- statement:
--   Consider the countable-state controlled Markov process of §5 with bounded cost, $c(i,a)\le M$ for every $i$ and $a\in U(i)$, under Ross's recurrence condition (5.7): $E^f_i[\tau]<K$ for all $f\in\Pi_{SD}$ and $i\in S$, where $\tau=\min\{t\ge1:X_t=0\}$ and $K>0$. Then for every $\beta\in(0,1)$ and every state $i$,
--   $$J^*_\beta(0)-J^*_\beta(i)\ \le\ (1-\beta^K)\,J^*_\beta(0)\ \le\ (1-\beta^K)\frac{M}{1-\beta}\ \le\ MK.$$
--
--   Together with (5.9), this bounds $|h_\beta(i)|$ by $MK$.
--
--   **Formalization Note.** The last inequality needs $K\ge1$, which is not a separate hypothesis: since $\tau\ge1$, (5.7) forces $K>1$. Under bounded cost $J^*_\beta$ is finite, so its value is used as a real number.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 302, proof of Theorem 5.3, (5.10)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Display (5.10) (proof of Theorem 5.3, p. 302): under bounded costs `c ≤ M₀` and (5.7), for every
`β ∈ (0, 1)` and every state `i`,
`J*_β(0) − J*_β(i) ≤ (1 − β^K) J*_β(0) ≤ (1 − β^K) M₀/(1 − β) ≤ M₀ K`. -/
theorem eq_5_10 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    (discValue M β 0).toReal - (discValue M β i).toReal ≤ (1 - β ^ K) * (discValue M β 0).toReal ∧
      (1 - β ^ K) * (discValue M β 0).toReal ≤ (1 - β ^ K) * (M₀ / (1 - β)) ∧
      (1 - β ^ K) * (M₀ / (1 - β)) ≤ M₀ * K := by sorry

end ArapostathisAC.RossRecurrence
