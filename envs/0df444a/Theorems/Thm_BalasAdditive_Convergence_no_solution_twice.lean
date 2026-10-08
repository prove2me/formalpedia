-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_no_solution_twice
-- name    : BalasAdditive.Convergence.no_solution_twice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:34:57.461003+00:00
-- url     : https://prove2.me/theorems/4e9877c1-88a6-4f89-9b8c-d7ec507bf059
-- title:
--   Convergence Theorem 2(b) — no solution is generated twice
-- statement:
--   At every reachable state of the additive algorithm, the generated assignments are pairwise distinct:
--
--   $$p<q\le s\ \Longrightarrow\ J_p\ne J_q.$$
--
--   This is part (b) of the proof of the convergence theorem and supplies finiteness of the sequence of generated solutions because there are only finitely many binary assignments.
--
--   **Formalization Note** Equality of assignments is equality of their index sets $J_p$, since the slacks and objective value are determined by those sets.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 533, proof of Convergence Theorem 2, part (b), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Proof of Convergence Theorem 2, part (b), p. 533. -/
theorem no_solution_twice {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) :
    (σ.history.map Record.J).Nodup := by sorry

end BalasAdditive.Convergence
