-- Prove2me | Theorems.Thm_ConstATSP_Gap_theorem_2_4
-- name    : ConstATSP.Gap.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:47:27.847493+00:00
-- url     : https://prove2.me/theorems/681d0ed7-2ac9-4241-8942-1888a041bb60
-- title:
--   Theorem 2.4, p. 10 — reduction of ATSP to laminarly-weighted instances
-- statement:
--   Let $\alpha$ be a constant such that every laminarly-weighted ATSP instance $I'$ (on any finite vertex and edge sets, with at least two vertices) has a tour of weight at most $\alpha\,\mathrm{value}(I')$. Then for every strongly connected digraph $G=(V,E)$ with $|V|\ge2$, every nonnegative weight function $w$, and every feasible solution $x$ of LP$(G,w)$, there is a tour $F$ of $G$ with
--   $$\sum_{e\in E}F(e)\,w(e)\le\alpha\sum_{e\in E}w(e)\,x(e).$$
--   Equivalently, the general ATSP has a tour of weight at most $\alpha$ times the Held–Karp lower bound.
--
--   This is the first main step of the paper: it reduces ATSP with arbitrary weights to laminarly-weighted instances, where the weight of an edge is the sum of the dual values of the laminar sets it crosses.
--
--   **Formalization Note** The paper states this result for a polynomial-time algorithm. Running times are not formalized: following §11 of the paper, which derives the integrality gap "non-constructively", the algorithm is read existentially, i.e. as the existence of the object the algorithm would return. "At most $\alpha$ times the Held–Karp lower bound" is stated for every feasible $x$, which is equivalent because the minimum of LP$(G,w)$ is attained; no infimum is used. The assumed algorithm is a hypothesis quantified over instances on all finite types. $|V|\ge2$ is required: on one vertex without a loop no tour exists while LP$(G,w)$ has value $0$.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), p. 10, Theorem 2.4

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance

namespace ConstATSP.Gap

theorem theorem_2_4 (α : ℝ)
    (hA : ∀ {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] (I' : Instance V' E'),
      I'.IsValid → ∃ F : E' → ℕ, IsTour I'.G F ∧ I'.wt F ≤ α * I'.value)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (w : E → ℝ) (hV : 2 ≤ Fintype.card V) (hG : IsStronglyConnected G)
    (hw : ∀ e, 0 ≤ w e) (x : E → ℝ) (hx : IsHeldKarpFeasible G x) :
    ∃ F : E → ℕ, IsTour G F ∧ ∑ e, (F e : ℝ) * w e ≤ α * ∑ e, w e * x e := by sorry

end ConstATSP.Gap
