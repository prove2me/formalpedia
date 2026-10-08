-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_primal_limit
-- name    : BregmanPPA.IneqMult.primal_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:44.918142+00:00
-- url     : https://prove2.me/theorems/85bbb4eb-d0a3-4828-96b2-11d0082d1f2c
-- title:
--   Theorem 7 proof — feasibility, complementarity and Lagrangian optimality at primal limits
-- statement:
--   Assume an inequality multiplier run has multipliers converging to an optimal multiplier $p^*$, every $g_i$ is continuous on $C$, and the Bregman zone contains the closed nonnegative orthant. If $x^*$ is a subsequential limit of the primal iterates, then $x^*\in C$, every $g_i(x^*)\le0$, complementary slackness holds, and $x^*$ minimizes the Lagrangian over $C$:
--
--   $$\langle p^*,g(x^*)\rangle=0,\qquad f(x^*)+\langle p^*,g(x^*)\rangle\le f(y)+\langle p^*,g(y)\rangle\quad(y\in C).$$
--
--   These are the limiting conditions from which the primal-solution clause of Theorem 7 follows.
--
--   **Formalization Note** A limit point means the limit of a strictly increasing subsequence. Constraint values are finite on $C$, so their real vector representation is valid there.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 218–219, proof of Theorem 7, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Run

open Filter Topology

namespace BregmanPPA.IneqMult

/-- The limit point claim in the proof of Theorem 7, pp. 218–219. -/
theorem primal_limit {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m) (pstar : E m)
    (hP : IsConvexProgram C f g)
    (hd : ∃ q : E m, dualFn C f g q ≠ ⊥)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S)
    (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p)
    (hcont : ∀ i, ContinuousOn (g i) C)
    (hSbar : nonnegOrthant m ⊆ S)
    (hoptimal : IsOptimalMultiplier C f g pstar)
    (hp : Tendsto p atTop (𝓝 pstar)) :
    ∀ (φ : ℕ → ℕ) (xstar : E n), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 xstar) →
      xstar ∈ C ∧ (∀ i, g i xstar ≤ 0) ∧
      inner ℝ pstar (gvec g xstar) = 0 ∧
      (∀ y ∈ C,
        f xstar + ((inner ℝ pstar (gvec g xstar) : ℝ) : EReal) ≤
        f y + ((inner ℝ pstar (gvec g y) : ℝ) : EReal)) := by sorry

end BregmanPPA.IneqMult
