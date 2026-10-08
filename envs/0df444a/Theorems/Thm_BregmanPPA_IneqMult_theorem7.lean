-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_theorem7
-- name    : BregmanPPA.IneqMult.theorem7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:34.516187+00:00
-- url     : https://prove2.me/theorems/ca9208af-c24b-4083-b348-bea3fdd66144
-- title:
--   Theorem 7 — convergence of nonquadratic inequality multipliers
-- statement:
--   Consider problem (10) with closed nonempty convex $C$, proper lower semicontinuous convex $f,g_1,\ldots,g_m$ finite on $C$, and a dual functional not identically $-\infty$. Let $h$ be a Bregman function whose zone and gradient image contain the strictly positive orthant. Let $(c_k)$ be positive with a positive lower bound, and let $(x^k,p^k)$ satisfy recursion (11). Then:
--
--   $$\begin{aligned}
--   \exists p^*\in\operatorname*{argmax}d&\Longrightarrow p^k\to\text{some optimal }p^*,\\
--   \exists p^*\in\operatorname*{argmax}d,\quad g_i\text{ continuous on }C,\quad\overline{\Omega^+}\subseteq S&\Longrightarrow\text{every primal limit point solves (10)},\\
--   \operatorname*{argmax}d=\varnothing,\quad\overline{\Omega^+}\subseteq S&\Longrightarrow\{p^k\}\text{ is unbounded}.
--   \end{aligned}$$
--
--   This is the paper's convergence and divergence result for a nonquadratic method of multipliers with inequality constraints.
--
--   **Formalization Note** The paper prints “if (10) has no solution” in the last clause; its proof on p. 218 establishes the no-optimal-multiplier premise, and that is the statement formalized. The second clause is the paper's “convergent case” and thus explicitly assumes an optimal multiplier. The closed-orthant zone condition applies only to the last two clauses. A limit point is a subsequential limit, and unboundedness concerns the range of the full multiplier sequence.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 216–218, Theorem 7 and proof, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_IneqMult_Run

open Filter Topology

namespace BregmanPPA.IneqMult

/-- Theorem 7, p. 216, with its final condition corrected to the condition proved on p. 218. -/
theorem theorem7 {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hP : IsConvexProgram C f g)
    (hd : ∃ q : E m, dualFn C f g q ≠ ⊥)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S)
    (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p) :
    ((∃ q : E m, IsOptimalMultiplier C f g q) →
      ∃ pstar : E m, IsOptimalMultiplier C f g pstar ∧ Tendsto p atTop (𝓝 pstar)) ∧
    ((∃ q : E m, IsOptimalMultiplier C f g q) →
      (∀ i, ContinuousOn (g i) C) → nonnegOrthant m ⊆ S →
      ∀ (φ : ℕ → ℕ) (xstar : E n), StrictMono φ →
        Tendsto (x ∘ φ) atTop (𝓝 xstar) → IsSolution C f g xstar) ∧
    ((¬ ∃ q : E m, IsOptimalMultiplier C f g q) →
      nonnegOrthant m ⊆ S → ¬ Bornology.IsBounded (Set.range p)) := by sorry

end BregmanPPA.IneqMult
