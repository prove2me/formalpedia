-- Prove2me | Theorems.Thm_BHTOpinion_Discrete_proposition1_average_variance
-- name    : BHTOpinion.Discrete.proposition1_average_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:46.284413+00:00
-- url     : https://prove2.me/theorems/5023ef4a-8f9d-4173-bead-f88de7fecb9d
-- title:
--   Proposition 1 — the average opinion is constant, V is nonincreasing, and dV/dt < 0 off F (= 0 on F) except at countably many times
-- statement:
--   Let $n\ge1$ and let $x$ be a proper solution of (2.1). Write $\bar x(t)=\frac1n\sum_{i=1}^n x_i(t)$ for the average opinion and
--
--   $$V(x(t))=\sum_{i=1}^n\bigl(x_i(t)-\bar x(t)\bigr)^2$$
--
--   for the sum of squared differences from the average. Then:
--
--   1. the average $\bar x(t)$ is constant on $[0,\infty)$;
--   2. $t\mapsto V(x(t))$ is nonincreasing on $[0,\infty)$;
--   3. there is a countable set $S$ of times such that at every $t>0$ outside $S$ the function $t\mapsto V(x(t))$ is differentiable, and its derivative is negative if $x(t)\notin F$ and zero if $x(t)\in F$.
--
--   Average preservation and the decrease of $V$ are the two structural facts (both consequences of the symmetry of the interaction) that the paper's convergence argument and its continuum analogue rest on.
--
--   **Formalization Note** The paper writes "with the exception of a countable set of times"; this is formalized as the existence of a countable set $S$ outside of which the derivative exists and has the stated sign. The hypothesis $n\ge1$ is the paper's implicit convention (agents labelled $1,\dots,n$); it is added so that $\frac1n$ is meaningful. Times $t>0$ are used in item 3 because the trajectory is only meaningful on $[0,\infty)$; a countable exceptional set may contain $0$ anyway.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Proposition 1, p. 5218 (proof pp. 5218–5219)

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

namespace BHTOpinion.Discrete

theorem proposition1_average_variance {n : ℕ} (hn : 0 < n) (x : ℝ → Fin n → ℝ)
    (hx : IsProperSolution x) :
    (∀ t : ℝ, 0 ≤ t → avg (x t) = avg (x 0)) ∧
      AntitoneOn (fun t => V (x t)) (Set.Ici 0) ∧
      ∃ S : Set ℝ, S.Countable ∧ ∀ t : ℝ, 0 < t → t ∉ S →
        ∃ d : ℝ, HasDerivAt (fun s => V (x s)) d t ∧
          (x t ∉ F n → d < 0) ∧ (x t ∈ F n → d = 0) := by sorry

end BHTOpinion.Discrete
