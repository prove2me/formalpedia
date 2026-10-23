-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_lemma_5
-- name    : CTJMDP.MarkovSuff.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:33.10072+00:00
-- url     : https://prove2.me/theorems/1d3eed6b-72b7-4c3f-971d-3721a210d4b9
-- title:
--   Lemma 5, p. 14 — Theorem 1 for γ = δ_x: P^ϕ_x(t,Z,B) ≤ P^π_x(t,Z,B), with equality on ]0,s] when P^ϕ_x(s,X)=1
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$, let $\pi$ be a policy, and let $\phi$ be a Markov policy satisfying (16) for the initial distribution $\delta_x$ and $\pi$:
--   $P^\pi_x(t,Z,B)=\int_Z\phi(B\mid z,t)P^\pi_x(t,dz)$ for $t>0$ and measurable $Z,B$. Then
--   $$P^\phi_x(t,Z,B)\le P^\pi_x(t,Z,B),\qquad t>0,\ Z\in\mathfrak B(X),\ B\in\mathfrak B(A).$$
--   Moreover, if $P^\phi_x(s,X)=1$ for some $s>0$, equality holds for all $t\in\,]0,s]$; and if $P^\phi_x(t,X)=1$ for all $t>0$, equality holds for all $t>0$.
--
--   This is Theorem 1 when the initial distribution is concentrated at a single state; the general case is reduced to it through the extended model.
--
--   **Formalization Note** The initial distribution concentrated at $x$ is the Dirac measure $\delta_x$ (on a standard Borel space, $\gamma(\{x\})=1$ means $\gamma=\delta_x$).
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 14, Lemma 5 (Theorem 1, p. 7, with γ({x}) = 1)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Lemma 5 (p. 14): Theorem 1 for an initial distribution concentrated at a point `x`. -/
theorem lemma_5 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M (Measure.dirac x) π Ppi)
    (hPphi : IsLaw M (Measure.dirac x) (markovPol phi) Pphi)
    (h16 : Disintegrates Ppi π phi) :
    (∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
      saMarg Pphi (markovPol phi) t Z B ≤ saMarg Ppi π t Z B) ∧
    (∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) ∧
    ((∀ t : ℝ, 0 < t → stateMarg Pphi t univ = 1) →
      ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) := by sorry

end CTJMDP.MarkovSuff
