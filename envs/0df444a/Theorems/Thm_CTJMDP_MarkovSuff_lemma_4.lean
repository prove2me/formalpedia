-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_lemma_4
-- name    : CTJMDP.MarkovSuff.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:34.283027+00:00
-- url     : https://prove2.me/theorems/863b40f3-f162-4426-85f6-218f0da67f33
-- title:
--   Lemma 4, p. 12 — the forward identity (37) holds for every (x, π)-bounded set, even for explosive processes
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$, let $\pi$ be a policy and $\mathbb P^\pi_x$ its law. A measurable set $Z$ is **$(x,\pi)$-bounded** (Definition 2) if $\sup_{t>0}\mathbb E^\pi_x\,\tilde q(\xi_t,\pi_t)I\{\xi_t\in Z\}<\infty$. If $Z$ is $(x,\pi)$-bounded, then for every $t>0$
--   $$P^\pi_x(t,Z)=\delta_x(Z)+\mathbb E^\pi_x\int_0^t\tilde q(\xi_s,\pi_s,Z\setminus\{\xi_s\})I\{\xi_s\in X\}\,ds-\mathbb E^\pi_x\int_0^t\tilde q(\xi_s,\pi_s)I\{\xi_s\in Z\}\,ds,\qquad(37)$$
--   with both expectations finite.
--
--   Lemma 4 extends to possibly explosive processes and to $(x,\pi)$-bounded sets the forward identities of Kitaev, Guo–Song and Piunovskiy–Zhang; it is the step that shows the marginals of an arbitrary policy solve Kolmogorov's forward equation of the induced Markov policy.
--
--   **Formalization Note** (37) is stated additively in $[0,\infty]$, $P^\pi_x(t,Z)+\mathbb E\tilde\nu^\pi([0,t],Z)=\delta_x(Z)+\mathbb E\nu^\pi([0,t],Z)$, together with $\mathbb E\tilde\nu^\pi([0,t],Z)<\infty$; since $P^\pi_x(t,Z)\le1$ this forces the other expectation to be finite and is equivalent to the real equation.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 12, Lemma 4; Definition 2 and (37), p. 11

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Lemma 4 (p. 12): (37) holds for every `(x, π)`-bounded set `Z`. -/
theorem lemma_4 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) π P)
    (Z : Set X) (hZ : MeasurableSet Z) (hbdd : IsBoundedFor M P π Z) :
    ∀ t : ℝ, 0 < t →
      EnuTilde M P π t Z < ⊤ ∧
      stateMarg P t Z + EnuTilde M P π t Z = Measure.dirac x Z + EnuPi M P π t Z := by sorry

end CTJMDP.MarkovSuff
