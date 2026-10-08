-- Prove2me | Theorems.Thm_FixpNash_DivFree_threshold_spec
-- name    : FixpNash.DivFree.threshold_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:37.868957+00:00
-- url     : https://prove2.me/theorems/7d3d49ec-33a9-44b1-a8d6-029dd6d199b5
-- title:
--   p. 47 — f_{i,x}(t) = 1 has a unique solution t_i
-- statement:
--   Fix a finite game, a real vector $x$ indexed by player–strategy pairs, and a player $i$ whose strategy set $S_i$ is nonempty. Let $h_{ij}(x)=x_{ij}+u_i((i{:}j);x_{-i})$ and $f_{i,x}(t)=\sum_{j\in S_i}\max(h_{ij}(x)-t,0)$. Then the equation $f_{i,x}(t)=1$ has exactly one real solution, and it is the threshold $t_i=\inf\{t: f_{i,x}(t)\le 1\}$:
--   $$f_{i,x}(t_i)=1\qquad\text{and}\qquad \forall t\in\mathbb R,\; f_{i,x}(t)=1\implies t=t_i.$$
--
--   The paper observes that $f_{i,x}$ is continuous, piecewise linear, equal to $+\infty$ in the limit $t\to-\infty$, strictly decreasing up to $\max_j h_{ij}(x)$ and $0$ from there on, and concludes that there is a unique $t_i$ with $f_{i,x}(t_i)=1$. This statement certifies that the threshold used in the definition of $G_I$ is that value.
--
--   **Formalization Note.** The statement holds for every real vector $x$, not only for mixed profiles. The hypothesis $S_i\neq\emptyset$ is the paper's tacit assumption: with $S_i=\emptyset$ the function $f_{i,x}$ is identically $0$ and no threshold exists.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, definition of G_I, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- p. 47: for a player with a nonempty strategy set, `f_{i,x}(t) = 1` has exactly one
solution `t`, and it is `threshold u x i`. Holds for every real vector `x`. -/
theorem threshold_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) (i : ι) (hi : Nonempty (S i)) :
    fSum u x i (threshold u x i) = 1 ∧
      ∀ t : ℝ, fSum u x i t = 1 → t = threshold u x i := by sorry

end FixpNash.DivFree
