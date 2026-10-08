-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_feasible_solution_no_improving
-- name    : BalasAdditive.Convergence.feasible_solution_no_improving
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:35:26.566438+00:00
-- url     : https://prove2.me/theorems/54bf6480-3e96-4095-84bc-8a2adfa9d77b
-- title:
--   Remark after (16) — a feasible generated solution has no improving vectors
-- statement:
--   Run the additive algorithm on an instance of problem $P$ (with $c\ge 0$) and let $u^p$ be any solution it has generated, with improving set $N_p$ formed by (16) at the moment $u^p$ was obtained,
--
--   $$N_p=N-(C^p\cup D_p\cup E_p).$$
--
--   If $u^p$ is feasible ($y^p\ge 0$), then
--
--   $$N_p=\varnothing .$$
--
--   The remark is a consistency check of the definitions (14)–(16) and of the ceiling (9)–(10): once a feasible solution has been reached, no index can be added to it without hitting the ceiling.
--
--   **Formalization Note** The statement is for every state reachable from the initial state (19) and every generated index $p\le s$; $N_p$ is the set stored when $u^p$ was obtained.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 524, remark after Eq. (16), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Remark after (16), p. 524: the improving set `N_p` formed for a feasible
generated solution `u^p` is empty. -/
theorem feasible_solution_no_improving {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (p : ℕ) (hp : p < σ.history.length)
    (hfeas : P.lp.Feasible (σ.J p)) :
    σ.N p = ∅ := by sorry

end BalasAdditive.Convergence
