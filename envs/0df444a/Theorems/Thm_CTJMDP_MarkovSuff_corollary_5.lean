-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_corollary_5
-- name    : CTJMDP.MarkovSuff.corollary_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:24.708836+00:00
-- url     : https://prove2.me/theorems/b10c3de5-67b6-453e-bf43-a658583e6448
-- title:
--   Corollary 5, p. 10 — P^ϕ_x is the minimal solution of Kolmogorov's forward equation (32), unique among [0,1]-valued solutions on ]0,s] when P^ϕ_x(s,X)=1
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$, let $\phi$ be a Markov policy and $\mathbb P^\phi_x$ its law. Consider Kolmogorov's forward equation for $\phi$,
--   $$P(t,Z)=\delta_x(Z)+\int_0^t\!\int_X\tilde q(z,\phi_s,Z\setminus\{z\})P(s,dz)\,ds-\int_0^t\!\int_Z\tilde q(z,\phi_s)P(s,dz)\,ds,\qquad(32)$$
--   required for $t>0$ and $Z\in\mathcal Y^\phi=\{Z:\sup_{z\in Z,t>0}\tilde q(z,\phi_t)<\infty\}$ (33), a solution being a family of measures $P(t,\cdot)$, measurable in $t$ (Definition 1). Then:
--
--   1. $P^\phi_x(t,Z)$ is a solution of (32), and $P^\phi_x(t,Z)\le P(t,Z)$ for every solution $P$, all $t>0$ and measurable $Z$;
--   2. if $P^\phi_x(s,X)=1$ for some $s>0$, then $P(t,Z)=P^\phi_x(t,Z)$ for $t\in\,]0,s]$ and every measurable $Z$, for every solution $P$ with values in $[0,1]$;
--   3. if $P^\phi_x(t,X)=1$ for all $t>0$, then $P^\phi_x$ is the unique solution of (32) with values in $[0,1]$.
--
--   In the proof of Theorem 1 this is the comparison principle: the marginal of the induced Markov policy is dominated by any other solution, in particular by the marginal of the original policy.
--
--   **Formalization Note** (32) is written additively in $[0,\infty]$ with the subtracted integral finite; solutions are families of finite measures.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 10, Corollary 5, (32)–(33); Definition 1, p. 9

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Corollary 5 (p. 10): `P^ϕ_x` is the minimal solution of (32), and the unique `[0, 1]`-valued one
on `]0, s]` when `P^ϕ_x(s, X) = 1`. -/
theorem corollary_5 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) (markovPol phi) P) :
    IsFwdSol M phi x (stateMarg P) ∧
    (∀ Q : ℝ → Measure X, IsFwdSol M phi x Q →
      ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → stateMarg P t Z ≤ Q t Z) ∧
    (∀ s : ℝ, 0 < s → stateMarg P s univ = 1 →
      ∀ Q : ℝ → Measure X, IsFwdSol M phi x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
        ∀ t ∈ Ioc (0 : ℝ) s, ∀ Z : Set X, MeasurableSet Z → Q t Z = stateMarg P t Z) ∧
    ((∀ t : ℝ, 0 < t → stateMarg P t univ = 1) →
      ∀ Q : ℝ → Measure X, IsFwdSol M phi x Q → (∀ t : ℝ, 0 < t → Q t univ ≤ 1) →
        ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → Q t Z = stateMarg P t Z) := by sorry

end CTJMDP.MarkovSuff
