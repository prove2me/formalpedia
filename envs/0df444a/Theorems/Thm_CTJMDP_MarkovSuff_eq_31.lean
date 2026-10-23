-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_eq_31
-- name    : CTJMDP.MarkovSuff.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:29.805979+00:00
-- url     : https://prove2.me/theorems/d4a5025b-ac84-4a58-91f0-4febd10305da
-- title:
--   (31), p. 10 — the state marginal P^ϕ_x(t,Z) of a Markov policy equals Feller's transition function P^ϕ(0,x;t,Z)
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\phi$ be a Markov policy, $x\in X$, and $\mathbb P^\phi_x$ the law of the process under $\phi$ from $x$. Let $P^\phi(u,x;t,Z)$ be Feller's series (25)–(27) for the Q-function $q(z,t,Z)=\tilde q(z,\phi_t,Z)$. Then, for every $t>0$ and measurable $Z$,
--   $$P^\phi_x(t,Z)=\mathbb P^\phi_x(\xi_t\in Z)=P^\phi(0,x;t,Z).\qquad(31)$$
--
--   This identifies the state marginal of a Markov policy with Feller's minimal transition function, and is how Corollary 5 follows from Theorem 3.
--
--   **Formalization Note** The paper derives (31) from Corollary 4 (the process under $\phi$ is a jump Markov process with transition function $P^\phi$); only the consequence (31) is stated.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 10, (31) (from Corollary 4)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- (31) (p. 10, from Corollary 4): `P^ϕ_x(t, Z) = P^ϕ(0, x; t, Z)`. -/
theorem eq_31 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) (markovPol phi) P) :
    ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z →
      stateMarg P t Z = fellerSeries (qOf M phi) 0 x t Z := by sorry

end CTJMDP.MarkovSuff
