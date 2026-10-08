-- Prove2me | Theorems.Thm_CouplingHMC_Exact_lemma_3_2_exact
-- name    : CouplingHMC.Exact.lemma_3_2_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:31.886696+00:00
-- url     : https://prove2.me/theorems/09e5c5eb-923e-4f82-84b8-a34a39991b51
-- title:
--   Lemma 3.2, case h = 0, p. 20 — first-variation bounds (51)–(52) for the exact Hamiltonian flow under Lt² ≤ 1
-- statement:
--   Suppose Assumption 2.1 holds, let $(q_t,p_t)$ be the exact Hamiltonian flow and let $t\ge0$ with $Lt^2\le1$. For all $x,y,u,v\in\mathbb R^d$, writing $m=\max\bigl(|x-y|,|(x-y)+t(u-v)|\bigr)$,
--
--   1. (51) $\displaystyle\max_{s\le t}|q_s(x,u)-q_s(y,v)-(x-y)-s(u-v)|\le Lt^2\,m$;
--   2. (52) $\displaystyle\max_{s\le t}|p_s(x,u)-p_s(y,v)-(u-v)|\le Lt\max_{s\le t}|q_s(x,u)-q_s(y,v)|\le Lt(1+Lt^2)\,m$.
--
--   The maxima run over $s\in[0,t]$. On short time intervals the difference of two Hamiltonian trajectories stays close to the difference of the corresponding straight-line motions.
--
--   **Formalization Note.** This is the case $h=0$ of the paper's lemma. The middle term of (52) is stated through an arbitrary bound $B$ of $|q_s(x,u)-q_s(y,v)|$ on $[0,t]$: every such $B$ gives $|p_s(x,u)-p_s(y,v)-(u-v)|\le LtB$. This avoids a real supremum, which would be $0$ on an unbounded set. The condition $Lt^2\le1$ is the standing assumption (46) of §3.1 at $h=0$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Lemma 3.2, (51)–(52), with (46), p. 20

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- Lemma 3.2 (p. 20), case `h = 0`: for the exact flow and `t ≥ 0` with `Lt² ≤ 1` ((46)),
(51) `max_{s≤t} |q_s(x,u) - q_s(y,v) - (x-y) - s(u-v)| ≤ Lt² max(|x-y|, |(x-y) + t(u-v)|)`;
(52) `max_{s≤t} |p_s(x,u) - p_s(y,v) - (u-v)| ≤ Lt max_{s≤t} |q_s(x,u) - q_s(y,v)|
      ≤ Lt(1 + Lt²) max(|x-y|, |(x-y) + t(u-v)|)`.
The middle maximum is expressed through an arbitrary bound `B` of `|q_s(x,u) - q_s(y,v)|` on `[0, t]`. -/
theorem lemma_3_2_exact {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (t : ℝ) (ht : 0 ≤ t)
    (h46 : L * t ^ 2 ≤ 1) (x y u v : E d) :
    (∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖q s x u - q s y v - (x - y) - s • (u - v)‖ ≤
        L * t ^ 2 * max ‖x - y‖ ‖(x - y) + t • (u - v)‖) ∧
    (∀ B : ℝ, (∀ r ∈ Set.Icc (0 : ℝ) t, ‖q r x u - q r y v‖ ≤ B) →
      ∀ s ∈ Set.Icc (0 : ℝ) t, ‖p s x u - p s y v - (u - v)‖ ≤ L * t * B) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖p s x u - p s y v - (u - v)‖ ≤
        L * t * (1 + L * t ^ 2) * max ‖x - y‖ ‖(x - y) + t • (u - v)‖) := by sorry

end CouplingHMC.Exact
