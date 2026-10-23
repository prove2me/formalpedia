-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_corollary_1
-- name    : CTJMDP.MarkovSuff.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:41.343412+00:00
-- url     : https://prove2.me/theorems/ec840275-7c1d-4813-8735-03a3aa1b956c
-- title:
--   Corollary 1, p. 7 — a Markov policy satisfies (16) iff ϕ(B|z,t) = P^π_γ(t,dz,B)/P^π_γ(t,dz) a.s. (19)
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution, $\pi$ a policy with law $\mathbb P^\pi_\gamma$, and $\phi$ a Markov policy. Then $\phi$ satisfies (16) for $(\gamma,\pi)$ if and only if, for every $t>0$ and every measurable $B\subseteq A$,
--   $$\phi(B\mid z,t)=\frac{P^\pi_\gamma(t,dz,B)}{P^\pi_\gamma(t,dz)}\qquad\text{for }P^\pi_\gamma(t,\cdot)\text{-almost every }z\in X,\qquad(19)$$
--   the right-hand side being the Radon–Nikodym derivative of the measure $Z\mapsto P^\pi_\gamma(t,Z,B)$ with respect to $P^\pi_\gamma(t,\cdot)$.
--
--   Corollary 1 identifies the Markov policy of Lemma 1 up to null sets; it is how (16) is checked for the extended policies in the proof of Theorem 1.
--
--   **Formalization Note** It is stated for every Markov policy $\phi$; the phrase "whose existence is stated in Lemma 1" in the paper names $\phi$ and adds no hypothesis.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 7, Corollary 1, (19)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Corollary 1 (p. 7): a Markov policy satisfies (16) iff it is the Radon–Nikodym derivative (19). -/
theorem corollary_1 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi) :
    Disintegrates P π phi ↔
      ∀ t : ℝ, 0 < t → ∀ B : Set A, MeasurableSet B →
        (fun z => phi z t B) =ᵐ[stateMarg P t] (saMargMeas P π t B).rnDeriv (stateMarg P t) := by sorry

end CTJMDP.MarkovSuff
