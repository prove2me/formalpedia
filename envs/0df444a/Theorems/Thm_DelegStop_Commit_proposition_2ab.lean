-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_2ab
-- name    : DelegStop.Commit.proposition_2ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:09.696194+00:00
-- url     : https://prove2.me/theorems/83aee7e2-7a00-41f6-b64c-72fec4562cea
-- title:
--   Proposition 2 (a)–(b), p. 6323 (PDF 8) — the flexible client stops iff v₁ ≥ v^F_s, for a unique threshold v^F_s ≥ 0
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2 ($0 < \mu_l < \mu_h < 1$, $0 \le c_l < c_h$, $c_h/\mu_h \ge c_l/\mu_l$, $k > 0$), with evaluation cost $c_I > 0$ and payment $p > 0$. Under the flexible stopping policy, after a feasible first solution of quality $v_1 > 0$ the client stops if stopping, worth $v_1 - p$, is at least as good as continuing, against the round-2 effort $\mu^{F+}_2$ the provider then chooses.
--
--   **Proposition 2 (a)–(b).** There is a unique $v^F_s \ge 0$ such that, for every $v_1 > 0$,
--   $$\text{the client stops} \iff v_1 \ge v^F_s .$$
--   That is, the client stops and takes the first solution if $v_1 \ge v^F_s$, and continues and seeks another solution if $v_1 < v^F_s$.
--
--   The threshold $v^F_s$ is the object through which the flexible policy affects the provider's first-round effort (Proposition 3 (b)).
--
--   **Formalization Note.** Only $T = 2$ is modelled. The statement is for feasible $v_1 > 0$: rule (1) applies only after a feasible solution, and after an infeasible one ($v_1 = 0$), rule (2) continues the project. The model does not define $v^F_s$; its existence and uniqueness are the content of the theorem. $c_I > 0$ is assumed: at $c_I = 0$ the client never stops after round 1, and the page's threshold would be $+\infty$.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6323 (PDF 8), Proposition 2 (a)–(b)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_2ab (P : Params) (hP : P.Standing) (cI p : ℝ) (hcI : 0 < cI) (hp : 0 < p) :
    ∃! vs : ℝ, IsStopThreshold P cI p vs := by sorry

end DelegStop.Commit
