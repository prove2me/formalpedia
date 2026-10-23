-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_compensator_eq_8
-- name    : CTJMDP.MarkovSuff.compensator_eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:59.165094+00:00
-- url     : https://prove2.me/theorems/019186a7-08d8-4b3f-8cd7-1626679ed307
-- title:
--   (8), p. 5 — 𝔼^π_γ µ([0,T],Z) = 𝔼^π_γ ν^π([0,T],Z) for every stopping time T: ν^π compensates the jump measure µ
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be an initial distribution, $\pi$ a policy and $\mathbb P^\pi_\gamma$ its law. Let $\mu([0,t],Z)=\sum_{n\ge1}I\{t_n\le t\}I\{x_n\in Z\}$ be the number of jumps into $Z$ by time $t$, (7), and
--   $$\nu^\pi([0,t],Z)=\int_0^t\tilde q(\xi_s,\pi_s,Z\setminus\{\xi_s\})\,I\{\xi_s\in X\}\,ds,\qquad(9)$$
--   its candidate compensator. Let $\mathscr F_t=\sigma(\xi_s:0\le s\le t)$ be the natural filtration. Then, for every stopping time $T$ of $(\mathscr F_t)$ with values in $\mathbb R_+=]0,+\infty[$ and every measurable $Z\subseteq X$,
--   $$\mathbb E^\pi_\gamma\,\mu([0,T],Z)=\mathbb E^\pi_\gamma\,\nu^\pi([0,T],Z),$$
--   both sides possibly infinite.
--
--   This is property (8) of the compensator, used at $T=t$ in (41) of the proof of Lemma 4.
--
--   **Formalization Note** Property (i) of a compensator (predictability of $\nu^\pi$) holds by construction; the statement is property (ii), (8). Stopping times are taken with respect to the natural filtration $\sigma(\xi_s:0\le s\le t)$ on the trajectory space `X × (ℕ → ℝ≥0∞ × X)`, with $\xi_s=x_n$ for $t_n\le s<t_{n+1}$. The integrand uses $\xi_{s-}$, which differs from $\xi_s$ on a countable set of times.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 5, (7)–(9) and the paragraph after (9)

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- (8) for `(ℙ^π_γ, µ, ν^π)` (p. 5): `𝔼 µ([0, T], Z) = 𝔼 ν^π([0, T], Z)` for every stopping time `T` of
the natural filtration with values in `ℝ₊` and every `Z ∈ 𝔅(X)`. -/
theorem compensator_eq_8 {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π)
    (P : Measure (Traj X)) (hP : IsLaw M gam π P) :
    ∀ T : Traj X → ℝ, IsStopTime T → ∀ Z : Set X, MeasurableSet Z →
      EmuAt P T Z = EnuPiAt M P π T Z := by sorry

end CTJMDP.MarkovSuff
