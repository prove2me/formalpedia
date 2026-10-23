-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_lemma_3
-- name    : CTJMDP.MarkovSuff.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:05.136373+00:00
-- url     : https://prove2.me/theorems/902bc75f-8731-48a3-a17c-b2693f034e63
-- title:
--   Lemma 3, p. 11 — 𝔼^π_x µ̃([0,T],Z) = 𝔼^π_x ν̃^π([0,T],Z) for every stopping time T: ν̃^π compensates the jumps out of Z
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $x\in X$ be an initial state, $\pi$ a policy and $\mathbb P^\pi_x$ its law. Let
--   $$\tilde\mu([0,t],Z)=\sum_{n\ge1}I\{t_n\in[0,t]\}I\{x_{n-1}\in Z\},\qquad \tilde\nu^\pi([0,t],Z)=\int_0^t\tilde q(\xi_s,\pi_s)\,I\{\xi_s\in Z\}\,ds,$$
--   the number of jumps out of $Z$ by time $t$, (36), and the cumulative intensity of jumping out of $Z$, (35). Then, for every stopping time $T$ of the natural filtration $\sigma(\xi_s:0\le s\le t)$ with values in $\mathbb R_+$ and every measurable $Z$,
--   $$\mathbb E^\pi_x\,\tilde\mu([0,T],Z)=\mathbb E^\pi_x\,\tilde\nu^\pi([0,T],Z).$$
--
--   Lemma 3 (Kitaev and Rykov) says $\tilde\nu^\pi$ is a compensator of $\tilde\mu$; it is used in (42) of the proof of Lemma 4.
--
--   **Formalization Note** As for (8): the compensator property is stated as (8) for every stopping time of the natural filtration (predictability of $\tilde\nu^\pi$ holds by construction).
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 11, Lemma 3, (35)–(36)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- Lemma 3 (p. 11): `ν̃^π` is a compensator of `µ̃` under `ℙ^π_x`, i.e. (8) holds for them:
`𝔼^π_x µ̃([0, T], Z) = 𝔼^π_x ν̃^π([0, T], Z)` for every stopping time `T` with values in `ℝ₊`. -/
theorem lemma_3 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (P : Measure (Traj X)) (hP : IsLaw M (Measure.dirac x) π P) :
    ∀ T : Traj X → ℝ, IsStopTime T → ∀ Z : Set X, MeasurableSet Z →
      EmuTildeAt P T Z = EnuTildeAt M P π T Z := by sorry

end CTJMDP.MarkovSuff
