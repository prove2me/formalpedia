-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_theorem_5_3_explicit
-- name    : ArapostathisAC.RossRecurrence.theorem_5_3_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:27:01.21527+00:00
-- url     : https://prove2.me/theorems/f64acb14-9922-4ab9-9325-83911df52e60
-- title:
--   Theorem 5.3 with the explicit bound |h_β(i)| ≤ MK
-- statement:
--   Consider the countable-state controlled Markov process of §5 with bounded cost, $c(i,a)\le M$ for every $i$ and $a\in U(i)$. Let $\tau=\min\{t\ge1:X_t=0\}$ and assume Ross's recurrence condition (5.7): there is $K>0$ with $E^f_i[\tau]<K$ for all $f\in\Pi_{SD}$ and $i\in S$. Then the differential discounted value function $h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$ satisfies
--   $$|h_\beta(i)|\le MK\qquad\text{for all }\beta\in(0,1),\ i\in S.$$
--
--   This is the bound the proof of Theorem 5.3 produces ("The desired result follows from (5.9) and (5.10)"). The bound depends only on the cost bound $M$ and the recurrence constant $K$.
--
--   **Formalization Note.** The paper's Theorem 5.3 asserts only that $h_\beta$ is bounded uniformly; this item states the explicit constant obtained in its proof, which is a stronger statement. Under bounded cost $J^*_\beta$ is finite, so $h_\beta$ is a genuine difference of real numbers.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 302, proof of Theorem 5.3, conclusion from (5.9) and (5.10)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Theorem 5.3 with the bound its proof gives (p. 302, "The desired result follows from (5.9) and
(5.10)"): under bounded costs `c ≤ M₀` and (5.7), `|h_β(i)| ≤ M₀ K` for all `β ∈ (0, 1)` and all
states `i`. -/
theorem theorem_5_3_explicit {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) :
    ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ M₀ * K := by sorry

end ArapostathisAC.RossRecurrence
