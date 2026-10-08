-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_eq_5_6
-- name    : ArapostathisAC.VanishingDiscount.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:17:08.17514+00:00
-- url     : https://prove2.me/theorems/bdbad6a2-bb78-411b-8b7d-1c7415f5c60b
-- title:
--   Equation (5.6) — the optimality equation for the differential discounted value function $h_\beta$
-- statement:
--   Consider the countable-state controlled Markov process of §5, fix $0<\beta<1$, and assume that the discounted value function $J^*_\beta(i)$ is finite for every state $i$. Let
--   $$h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$$
--   be the differential discounted value function. Then, for every $i\in S$,
--   $$(1-\beta)J^*_\beta(0)+h_\beta(i)=\min_{a\in U(i)}\Big\{c(i,a)+\beta\sum_{j\in S}P(j\mid i,a)\,h_\beta(j)\Big\}.$$
--   Here a series $\sum_j P(j\mid i,a)h_\beta(j)$ that does not converge has the value $+\infty$ (its terms are bounded below by $-P(j\mid i,a)J^*_\beta(0)$), and the minimum is attained at an action whose series converges.
--
--   Equation (5.6) is the discounted analogue of the average cost optimality equation; letting $\beta\to1$ in it is how (5.1) is derived in Theorem 5.2.
--
--   **Formalization Note.** The paper presupposes that $h_\beta$ is real valued; the finiteness of $J^*_\beta$ is a stated hypothesis because Lean's `toReal` sends $+\infty$ to $0$. The minimum is encoded in two clauses: some admissible action has a convergent series and attains equality, and every admissible action whose series converges gives a value at least the left-hand side (an action whose series diverges contributes $+\infty$ and needs no clause).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 301, (5.6) (with the DCOE display and the definition of h_β on the same page)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

namespace ArapostathisAC.VanishingDiscount

theorem eq_5_6 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hfin : ∀ i, discValue M β i ≠ ⊤) (i : ℕ) :
    (∃ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) ∧
      (1 - β) * (discValue M β 0).toReal + hRel M β i =
        M.c i a + β * ∑' j, prob M i a j * hRel M β j) ∧
    (∀ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) →
      (1 - β) * (discValue M β 0).toReal + hRel M β i ≤
        M.c i a + β * ∑' j, prob M i a j * hRel M β j) := by sorry

end ArapostathisAC.VanishingDiscount
