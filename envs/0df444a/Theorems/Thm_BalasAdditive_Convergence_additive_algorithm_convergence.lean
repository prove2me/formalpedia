-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_additive_algorithm_convergence
-- name    : BalasAdditive.Convergence.additive_algorithm_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:35:29.742973+00:00
-- url     : https://prove2.me/theorems/9fb93290-c6be-4514-ad87-3a9a544c58e1
-- title:
--   Convergence Theorem 2 — the additive algorithm terminates with an optimal solution or infeasibility
-- statement:
--   For every instance of Balas's problem $P$ with nonnegative costs, the additive algorithm starting from $J_0=\varnothing$ has no infinite run. Every reachable state before a stopping situation has an allowed next step. At any reachable stopped state, let $z^{*(s)}$ be the ceiling formed from the generated solutions. Then
--
--   $$z^{*(s)}=+\infty\ \Longrightarrow\ P\text{ is infeasible},$$
--
--   $$z^{*(s)}<+\infty\ \Longrightarrow\ \text{some generated }J_q\text{ attains }z^{*(s)},\text{ and every generated feasible }J_q\text{ at that cost is optimal for }P.$$
--
--   Thus the finite algorithm ends with either an optimal feasible solution or a valid infeasibility verdict, exactly the two outcomes of Convergence Theorem 2.
--
--   **Formalization Note** “In a finite number of iterations” is stated as the absence of an infinite transition run together with a successor for every reachable non-stopped state; this excludes a missing algorithm case from counting as termination. The verdict quantifies over all binary assignments, not only generated ones. The ceiling uses an explicit $+\infty$ value when no feasible solution has yet been generated, and tied choices remain nondeterministic.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 533, Convergence Theorem 2; p. 526, step 5a, DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Convergence Theorem 2, p. 533: finite, non-stuck execution and the
optimality or infeasibility verdict at a stop. -/
theorem additive_algorithm_convergence {n m : ℕ} (P : Problem n m) :
    (¬ ∃ run : ℕ → State n,
      run 0 = init P ∧ ∀ t, Step P (run t) (run (t + 1))) ∧
    (∀ σ : State n, Reachable P σ → σ.phase ≠ .stopped → ∃ τ, Step P σ τ) ∧
    (∀ σ : State n, Reachable P σ → σ.phase = .stopped →
      (ceiling P σ = ⊤ → ∀ J : Finset (Fin n), ¬ P.lp.Feasible J) ∧
      (ceiling P σ ≠ ⊤ →
        (∃ q, q < σ.history.length ∧ P.lp.Feasible (σ.J q) ∧
          (↑(P.lp.cost (σ.J q)) : WithTop ℝ) = ceiling P σ) ∧
        (∀ q, q < σ.history.length → P.lp.Feasible (σ.J q) →
          (↑(P.lp.cost (σ.J q)) : WithTop ℝ) = ceiling P σ →
          P.lp.Optimal (σ.J q)))) := by sorry

end BalasAdditive.Convergence
