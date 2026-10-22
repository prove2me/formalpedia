-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_2c
-- name    : DelegStop.Commit.proposition_2c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:16.60899+00:00
-- url     : https://prove2.me/theorems/18825390-d79f-4490-b07b-229a83da4200
-- title:
--   Proposition 2 (c), p. 6323 (PDF 8) — the stopping threshold v^F_s is nondecreasing in k and nonincreasing in c_I
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2, with evaluation cost $c_I > 0$ and payment $p > 0$, and let $v^F_s$ be the flexible client's stopping threshold of Proposition 2 (a)–(b).
--
--   **Proposition 2 (c).**
--   1. $v^F_s$ is nondecreasing in $k$: if $v_s$ is a threshold at capability $k$ and $v_s'$ is a threshold at capability $k' \ge k$, all other parameters equal, then $v_s \le v_s'$.
--   2. $v^F_s$ is nonincreasing in $c_I$: if $v_s$ is a threshold at evaluation cost $c_I$ and $v_s'$ is a threshold at $c_I' \ge c_I$, then $v_s' \le v_s$.
--
--   A more capable provider, or a cheaper evaluation, makes a second round more attractive, so the client holds out for better first solutions.
--
--   **Formalization Note.** Only $T = 2$ is modelled. The claims are stated for every pair of thresholds in the sense of Proposition 2 (a)–(b) (which are unique), so no threshold is defined in closed form.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6323 (PDF 8), Proposition 2 (c)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_2c (P : Params) (hP : P.Standing) (cI p : ℝ) (hcI : 0 < cI) (hp : 0 < p) :
    (∀ k₂ : ℝ, P.k ≤ k₂ → ∀ vs vs₂ : ℝ,
      IsStopThreshold P cI p vs → IsStopThreshold { P with k := k₂ } cI p vs₂ → vs ≤ vs₂) ∧
    (∀ cI₂ : ℝ, cI ≤ cI₂ → ∀ vs vs₂ : ℝ,
      IsStopThreshold P cI p vs → IsStopThreshold P cI₂ p vs₂ → vs₂ ≤ vs) := by sorry

end DelegStop.Commit
