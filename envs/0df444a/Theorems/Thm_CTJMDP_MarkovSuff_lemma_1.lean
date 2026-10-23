-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_lemma_1
-- name    : CTJMDP.MarkovSuff.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:35.291219+00:00
-- url     : https://prove2.me/theorems/f92553c1-66be-43a1-9777-04a0a977f002
-- title:
--   Lemma 1, p. 6 — for every γ and π there is a Markov policy ϕ satisfying (16)
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution and $\pi$ a policy with law $\mathbb P^\pi_\gamma$. Then there is a Markov policy $\phi$ such that, for all $t>0$,
--   $$P^\pi_\gamma(t,Z,B)=\int_Z\phi(B\mid z,t)\,P^\pi_\gamma(t,dz),\qquad Z\in\mathfrak B(X),\ B\in\mathfrak B(A).\qquad(16)$$
--
--   Lemma 1 provides the Markov policy of Theorem 1: at each time it chooses actions with the conditional distribution of the action given the current state under $\pi$. Together with Theorem 1 it gives the existence half of the sufficiency of Markov policies.
--
--   **Formalization Note** A Markov policy is a transition probability from $X\times\mathbb R_+$ to $A$, jointly measurable, with $\phi(A(z)\mid z,t)=1$ for all $z$ and $t>0$.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 6, Lemma 1, (16)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Lemma 1 (p. 6): some Markov policy satisfies (16). -/
theorem lemma_1 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P) :
    ∃ phi : X → ℝ → Measure A, IsMarkovPolicy M phi ∧ Disintegrates P π phi := by sorry

end CTJMDP.MarkovSuff
