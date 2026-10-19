-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_theorem_2
-- name    : ExAnteExPost.RPS.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:39.920813+00:00
-- url     : https://prove2.me/theorems/6cbae1bd-f898-4a00-8d14-0e3934f5c523
-- title:
--   Theorem 2, p. 11 — the randomized allocation of Recursive Probabilistic Serial is ex-ante envy-free and ex-post EF1
-- statement:
--   Let $N$ be a finite nonempty set of $n$ agents and $M$ a finite set of $m$ goods, with additive non-negative valuations $v_{i,g} \ge 0$. Run Recursive Probabilistic Serial (Algorithm 1): for $t = 1, \dots, \lceil m/n \rceil$, let every agent eat her favorite available good of $M^t$ for one unit of time, giving $X^t = \mathrm{Eating}(M^t, 1)$; decompose $X^t = \sum_k w^{t,k} A^{t,k}$ as in Theorem 1; sample $B^t = A^{t,k}$ with probability $w^{t,k}$; and set $M^{t+1} = M^t \setminus \bigcup_i B^t_i$, with $M^1 = M$. Let $\mathbf X$ be the resulting randomized allocation of $B_i = \bigcup_t B^t_i$. Then
--
--   1. $\mathbf X$ is **ex-ante envy-free**: the fractional allocation $X = \sum_k p^k B^k$ it implements satisfies $v_i(X_i) \ge v_i(X_h)$ for all agents $i, h$;
--   2. $\mathbf X$ is **ex-post EF1**: every integral allocation $B$ drawn with positive probability satisfies, for all $i, h$ with $B_h \ne \emptyset$,
--   $$v_i(B_i) \ge v_i(B_h \setminus \{j\}) \quad \text{for some } j \in B_h .$$
--
--   The statement holds for every way of breaking ties between equally valued goods and for every decomposition allowed by Theorem 1. It shows that ex-ante envy-freeness and ex-post envy-freeness up to one good are simultaneously achievable for indivisible goods, which a single deterministic allocation cannot offer.
--
--   **Formalization Note.** The ex-post part quantifies over allocations of positive probability: the paper's support lists all pairs, but Theorem 1 allows weight-zero terms, which are never drawn and on which EF1 can fail. The paper's assumption that every good is valued positively by some agent is a without-loss-of-generality convention not used by the proof, and is omitted, which makes the statement stronger. Ties are broken by an arbitrary fixed rule, and the decomposition of line 5 is an arbitrary rule satisfying the conclusions of Theorem 1; the statement is universally quantified over both.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 11, Theorem 2 (Algorithm 1, p. 10)

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Theorem 2, p. 11: the randomized allocation implemented by Algorithm 1 is ex-ante envy-free
and ex-post EF1, for every favorite-good tie-break and every decomposition rule allowed by
Theorem 1. -/
theorem theorem_2 [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D) :
    ExAnteEF I (algorithm1 pick D) ∧ ExPostEF1 I (algorithm1 pick D) := by sorry
end ExAnteExPost.RPS
