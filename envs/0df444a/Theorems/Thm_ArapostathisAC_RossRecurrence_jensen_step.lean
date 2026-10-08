-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_jensen_step
-- name    : ArapostathisAC.RossRecurrence.jensen_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:26:43.297024+00:00
-- url     : https://prove2.me/theorems/10330d4a-b703-4dc7-94f5-5c0ac2b54792
-- title:
--   Jensen step — J*_β(i) ≥ J*_β(0) E[β^τ] ≥ J*_β(0) β^K
-- statement:
--   Consider the countable-state controlled Markov process of §5 with bounded cost, $c(i,a)\le M$ for every $i$ and $a\in U(i)$, under Ross's recurrence condition (5.7): $E^f_i[\tau]<K$ for all $f\in\Pi_{SD}$ and $i\in S$, with $\tau=\min\{t\ge1:X_t=0\}$ and $K>0$. Let $\beta\in(0,1)$ and let $f_\beta\in\Pi_{SD}$ be $\beta$-discount optimal. Then for every state $i$,
--   $$J^*_\beta(i)\ \ge\ J^*_\beta(0)\,E^{f_\beta}_i[\beta^\tau]\ \ge\ J^*_\beta(0)\,\beta^K.$$
--
--   This is the unnumbered display after (5.9) in the proof of Theorem 5.3. It gives the lower half of the uniform bound on $h_\beta$.
--
--   **Formalization Note.** $\beta^\tau=0$ on $\{\tau=\infty\}$, and $\beta^K$ is a real power since $K$ is real. The two inequalities are stated as a conjunction in $[0,\infty]$. The bounded-cost hypothesis is the standing assumption of §5.1.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 302, proof of Theorem 5.3, display after (5.9)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- The Jensen step (proof of Theorem 5.3, p. 302, display after (5.9)): under bounded costs and
(5.7), for a `β`-discount optimal `f ∈ Π_SD`,
`J*_β(i) ≥ J*_β(0) E^f_i[β^τ] ≥ J*_β(0) β^K`. -/
theorem jensen_step {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : StationaryPolicy M) (hf : IsDiscOptimal M f β)
    (i : ℕ) :
    discValue M β 0 * expDiscAtReturn M f β i ≤ discValue M β i ∧
      discValue M β 0 * ENNReal.ofReal (β ^ K) ≤ discValue M β 0 * expDiscAtReturn M f β i := by sorry

end ArapostathisAC.RossRecurrence
