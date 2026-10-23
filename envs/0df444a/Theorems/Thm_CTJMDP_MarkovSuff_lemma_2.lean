-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_lemma_2
-- name    : CTJMDP.MarkovSuff.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:34.653543+00:00
-- url     : https://prove2.me/theorems/2e15a8c9-32f8-46ee-898d-5251641a9178
-- title:
--   Lemma 2, p. 11 — P^π_x and P^ϕ_x both solve (32) for ϕ; P^ϕ_x(t,Z) ≤ P^π_x(t,Z), with equality on ]0,s] when P^ϕ_x(s,X)=1
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$, let $\pi$ be a policy, and let $\phi$ be a Markov policy satisfying (16) for the initial distribution $\delta_x$ and $\pi$. Let $\mathbb P^\pi_x$ and $\mathbb P^\phi_x$ be the laws of the process under $\pi$ and under $\phi$. Then:
--
--   1. (i) both state marginals $P^\pi_x(t,Z)$ and $P^\phi_x(t,Z)$ are solutions of Kolmogorov's forward equation (32) with $\phi$;
--   2. (ii) for all $t>0$ and measurable $Z$,
--   $$P^\phi_x(t,Z)\le P^\pi_x(t,Z);\qquad(34)$$
--   3. (iii) if $P^\phi_x(s,X)=1$ for some $s>0$, then (34) holds with equality for $t\in\,]0,s]$; if $P^\phi_x(t,X)=1$ for all $t>0$, then (34) holds with equality for all $t>0$.
--
--   Lemma 2 is the state-marginal version of Theorem 1 for an initial state; Lemma 5 lifts it to state-action marginals.
--
--   **Formalization Note** "Solution" is Definition 1 (finite measures, measurable in $t$, (32) for $Z\in\mathcal Y^\phi$ written additively).
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 11, Lemma 2, (34)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Lemma 2 (p. 11). -/
theorem lemma_2 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M (Measure.dirac x) π Ppi)
    (hPphi : IsLaw M (Measure.dirac x) (markovPol phi) Pphi)
    (h16 : Disintegrates Ppi π phi) :
    (IsFwdSol M phi x (stateMarg Ppi) ∧ IsFwdSol M phi x (stateMarg Pphi)) ∧
    (∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z → stateMarg Pphi t Z ≤ stateMarg Ppi t Z) ∧
    (∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ Z : Set X, MeasurableSet Z → stateMarg Pphi t Z = stateMarg Ppi t Z) ∧
    ((∀ t : ℝ, 0 < t → stateMarg Pphi t univ = 1) →
      ∀ t : ℝ, 0 < t → ∀ Z : Set X, MeasurableSet Z →
        stateMarg Pphi t Z = stateMarg Ppi t Z) := by sorry

end CTJMDP.MarkovSuff
