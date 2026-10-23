-- Prove2me | Theorems.Thm_CTJMDP_MarkovSuff_law_exists_unique
-- name    : CTJMDP.MarkovSuff.law_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:07.791299+00:00
-- url     : https://prove2.me/theorems/fabc5f06-e191-4dfb-926c-db4e64f836ab
-- title:
--   §2, p. 5 — a policy π and an initial distribution γ define a unique law ℙ^π_γ of the jump process
-- statement:
--   Throughout, $X$ and $A$ are standard Borel spaces, $A(x)\subseteq A$ are the feasible action sets, $\tilde q$ are the transition rates of the CTJMDP, the standing assumptions (i)–(iv) of §2 hold, and Assumption 2.1 holds: $\bar q(x)=\sup_{a\in A(x)}\tilde q(x,a)<\infty$ for every $x\in X$.
--
--   Let $\gamma$ be a probability measure on $X$ and let $\pi$ be a policy. Then there is exactly one probability measure $\mathbb P^\pi_\gamma$ on the space of trajectories $\omega=(x_0,t_1,x_1,\dots)$ such that $x_0$ has law $\gamma$ and, for every $n$, conditionally on the history $(x_0,t_1,\dots,t_n,x_n)$ with $t_n<\infty$, the next jump $(t_{n+1},x_{n+1})$ has the law
--   $$\mathbb P(t_{n+1}-t_n\in ds,\ x_{n+1}\in dy\mid\cdots)=e^{-\int_0^s\tilde q(x_n,\pi_n(r))\,dr}\,\tilde q(x_n,\pi_n(s),dy\setminus\{x_n\})\,ds,$$
--   with $\pi_n(s)=\pi_n(\cdot\mid x_0,t_1,\dots,t_n,x_n,s)$, while $t_{n+1}=\infty$ with the remaining probability $e^{-\int_0^\infty\tilde q(x_n,\pi_n(r))\,dr}$, and $t_{n+1}=\infty$ whenever $t_n=\infty$.
--
--   This is the measure $\mathbb P^\pi_\gamma$ of §2, for which $\nu^\pi$ of (9) is the compensator of the jump measure $\mu$. Every other statement of the mission takes the law as a hypothesis; this statement shows that hypothesis is satisfiable and determines the law.
--
--   **Formalization Note** The paper obtains $\mathbb P^\pi_\gamma$ from Jacod's theorem on the compensator; the Lean statement characterizes it by the equivalent explicit kernel (75)–(76) of p. 20 (Ionescu-Tulcea), extended from nonrandomized to relaxed policies.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, p. 5, §2 (Jacod [14, Theorem 3.6]); explicit kernel (75)–(76), p. 20

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

/-- §2, p. 5: an initial distribution `γ` and a policy `π` define a unique law `ℙ^π_γ` of the jump
process. -/
theorem law_exists_unique {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (gam : Measure X) [IsProbabilityMeasure gam]
    (π : Policy X A) (hπ : IsPolicy M π) :
    ∃! P : Measure (Traj X), IsLaw M gam π P := by sorry

end CTJMDP.MarkovSuff
