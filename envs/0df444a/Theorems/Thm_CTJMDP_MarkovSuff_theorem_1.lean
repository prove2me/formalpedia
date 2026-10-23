-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_theorem_1
-- name    : CTJMDP.MarkovSuff.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:44.054142+00:00
-- url     : https://prove2.me/theorems/41249ee0-2df2-470b-8b7e-cb7637ed7070
-- title:
--   Theorem 1, p. 7 — the Markov policy ϕ of (16) has state-action marginals ≤ those of π, with equality on ]0,s] when P^ϕ_γ(s,X)=1
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution on $X$, $\pi$ a policy, and $\phi$ a Markov policy satisfying (16):
--   $$P^\pi_\gamma(t,Z,B)=\int_Z\phi(B\mid z,t)\,P^\pi_\gamma(t,dz),\qquad t>0,\ Z\in\mathfrak B(X),\ B\in\mathfrak B(A),$$
--   where $P^\pi_\gamma(t,Z,B)=\mathbb E^\pi_\gamma[I\{\xi_{t-}\in Z\}\pi(B\mid\omega,t)]$ and $P^\pi_\gamma(t,Z)=\mathbb P^\pi_\gamma(\xi_{t-}\in Z)$ are the state-action and state marginals. Then
--   $$P^\phi_\gamma(t,Z,B)\le P^\pi_\gamma(t,Z,B),\qquad t>0,\ Z\in\mathfrak B(X),\ B\in\mathfrak B(A).\qquad(20)$$
--   In addition, if $P^\phi_\gamma(s,X)=1$ for some $s>0$, then (20) holds with equality for all $t\in\,]0,s]$. In particular, if $P^\phi_\gamma(t,X)=1$ for all $t>0$ (the process under $\phi$ is nonexplosive), then (20) holds with equality.
--
--   This is the main result of the paper: for a continuous-time jump MDP with possibly unbounded transition rates and possibly explosive processes, the Markov policy obtained by conditioning the actions of an arbitrary policy on the current state and time has state-action marginals no larger than the original ones, and equal ones when it does not explode. It implies the sufficiency of Markov policies for expected total discounted, finite-horizon, average and constrained costs (§6).
--
--   **Formalization Note** The laws $\mathbb P^\pi_\gamma$ and $\mathbb P^\phi_\gamma$ enter as hypotheses characterized by the explicit sojourn/jump kernel (`IsLaw`); `law_exists_unique` shows each exists and is unique. Marginals take values in $[0,\infty]$ (they are at most $1$) and read the process at $\xi_{t-}$; $Z\subseteq X$ and $B\subseteq A$ never contain the cemetery points.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 7, Theorem 1, (16), (20)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Theorem 1 (p. 7). -/
theorem theorem_1 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M gam π Ppi)
    (hPphi : IsLaw M gam (markovPol phi) Pphi)
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
