-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_abandoned_no_better_completion
-- name    : BalasAdditive.Convergence.abandoned_no_better_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:35:08.521047+00:00
-- url     : https://prove2.me/theorems/4faa62ed-1510-4bb8-9f56-518f5f5ff21a
-- title:
--   Theorem 1 — an abandoned solution has no better feasible completion
-- statement:
--   Suppose the additive algorithm has **abandoned** a generated solution $u^k$ while processing iteration $s$ (with $u^0,\ldots,u^s$ generated): it has been instructed to check $N_p^s$ for some $p<k\le s$ in step 5, or to stop. There is no feasible binary assignment $J_t$ strictly containing $J_k$ whose cost is below the current ceiling:
--
--   $$\nexists J_t:\ J_k\subset J_t,\quad J_t\text{ feasible},\quad z(J_t)<z^{*(s)}.$$
--
--   This is the exclusion theorem used to justify the algorithm's abandonment and final verdict.
--
--   **Formalization Note** The printed theorem writes $z^{*(k)}$; the algorithm and proof require $z^{*(s)}$. The statement uses the current ceiling and applies only to reachable states. The printed version fails already for $n=m=1$, $A=(-1)$, $b=(-1)$, $c=(1)$: the run $\varnothing\to\{1\}$ (step 4a) stops at step 5a, abandoning $u^0$, while $J_1=\{1\}$ is feasible, contains $J_0$ strictly, and has $z_1=1<\infty=z^{*(0)}$.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 529, Theorem 1 (ceiling corrected from z^{*(k)} to z^{*(s)}), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Theorem 1, p. 529, with the current ceiling `z^{*(s)}` in place of
the printed `z^{*(k)}`; the latter is false for the paper's algorithm. -/
theorem abandoned_no_better_completion {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (k : ℕ) (habandoned : Abandoned P σ k) :
    ¬ ∃ J : Finset (Fin n), P.lp.Feasible J ∧ σ.J k ⊂ J ∧
      (↑(P.lp.cost J) : WithTop ℝ) < ceiling P σ := by sorry

end BalasAdditive.Convergence
