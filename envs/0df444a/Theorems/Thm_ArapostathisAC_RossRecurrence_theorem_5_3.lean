-- Prove2me | Theorems.Thm_ArapostathisAC_RossRecurrence_theorem_5_3
-- name    : ArapostathisAC.RossRecurrence.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:27:10.850715+00:00
-- url     : https://prove2.me/theorems/4c84d455-fe71-4c7c-88f2-b295950f22f5
-- title:
--   Theorem 5.3 (Ross) — uniformly bounded mean return times make h_β uniformly bounded
-- statement:
--   Consider the countable-state controlled Markov process of §5: state space $S=\{0,1,2,\dots\}$, nonempty compact admissible action sets $U(i)$, and a nonnegative cost $c(i,\cdot)$ and transition probabilities $P(j\mid i,\cdot)$ that are continuous on $U(i)$. As §5.1 assumes, the cost is bounded: $c(i,a)\le M$ for all $i$ and $a\in U(i)$. For $\beta\in(0,1)$, let $J^*_\beta(i)$ be the optimal $\beta$-discounted cost from state $i$ over all admissible policies, and let
--   $$h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$$
--   be the differential discounted value function. For $f\in\Pi_{SD}$, let $\tau=\min\{t\ge1:X_t=0\}$ be the return time to state $0$ of the process controlled by $f$.
--
--   **Theorem 5.3.** Suppose there is a constant $K>0$ such that
--   $$E^f_i[\tau]<K\qquad\text{for all } f\in\Pi_{SD} \text{ and all } i\in S. \tag{5.7}$$
--   Then $h_\beta(i)$ is bounded uniformly in $\beta\in(0,1)$ and $i\in S$: there is a constant $B$ with $|h_\beta(i)|\le B$ for all $\beta\in(0,1)$ and $i\in S$.
--
--   This recurrence condition, due to Ross, implies the hypothesis of Theorem 5.2. Theorem 5.2 then gives a bounded solution of the average cost optimality equation and an average optimal stationary policy.
--
--   **Formalization Note.** The bounded-cost hypothesis is the standing assumption of §5.1 ("In this section, we assume that $c(\cdot,\cdot)$ is bounded"). It makes $J^*_\beta$ finite, so $h_\beta$ is a genuine difference of real numbers. The return time is valued in $\mathbb N\cup\{\infty\}$ and counts from $t\ge1$, so it applies from $i=0$ too. Its mean is a lower Lebesgue integral, so (5.7) forces $\tau<\infty$ almost surely. $J^*_\beta$ is the infimum over all history-dependent randomized admissible policies. The bound $B$ is chosen before $\beta$ and $i$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 301–302, Theorem 5.3 (with the §5.1 standing assumption, p. 301)

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- Theorem 5.3 (Ross; pp. 301–302), under the standing assumption of §5.1 that the cost is bounded:
if the mean return time `E^f_i[τ]`, `τ = min{t ≥ 1 : X_t = 0}`, is below a constant `K > 0` for
every `f ∈ Π_SD` and every initial state `i` (5.7), then `h_β(i) = J*_β(i) − J*_β(0)` is bounded
uniformly in `β ∈ (0, 1)` and `i`. -/
theorem theorem_5_3 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) :
    ∃ B : ℝ, ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ B := by sorry

end ArapostathisAC.RossRecurrence
