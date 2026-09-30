-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_bonus_max_minimal_exec
-- name    : AlgMechDesign.CompBonus.bonus_max_minimal_exec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:07:30.70325+00:00
-- url     : https://prove2.me/theorems/f5ba51ce-a3f3-48de-82ee-2f8439c0bfe8
-- title:
--   Claim 5.2, proof — the bonus is maximized by executing in minimal time
-- statement:
--   Fix an allocation $x$, an agent $i$ of type $t^i$, and declarations $t^l$ of the other agents; write $t$ for the resulting profile. Let $\tilde t$ be any vector of actual times in which agent $i$ performs each of its tasks no faster than possible, $\tilde t_j \ge t^i_j$ for $j \in x^i$ (the other coordinates are arbitrary, since they are not used). Then
--   $$
--   -g\big(x, \mathrm{corr}^i(x, t, \tilde t)\big) \;\le\; -g\big(x, \mathrm{corr}^*(x, t)\big),
--   $$
--   and $\mathrm{corr}^*(x, t)$ is exactly the corrected time vector of agent $i$ when it performs its tasks in minimal time $\tilde t_j = t^i_j$.
--
--   In words: for every allocation, agent $i$'s bonus is maximized when it executes its assignments in minimal time. This is the second observation of the proof of Claim 5.2.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, proof of Claim 5.2, first paragraph, third sentence ("… and that for every allocation x the bonus for an agent i is maximized when executing its assignments in minimal time")

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Proof of Claim 5.2 (p. 188): for every allocation `x`, the bonus of agent `i`, whose true type
is `t i` and whose fellow agents declared `t l`, is maximized when `i` performs its tasks in
minimal time: for every vector of actual times `tt` with `t i j ≤ tt j` on the tasks of `i`,
`-g(x, corrⁱ(x, t, tt)) ≤ -g(x, corr*(x, t))`, and `corr*(x, t)` is `corrⁱ` at minimal times. -/
theorem bonus_max_minimal_exec {n k : ℕ} [NeZero n] (x : Fin k → Fin n)
    (t : Fin n → Fin k → ℝ) (i : Fin n) (tt : Fin k → ℝ)
    (htt : ∀ j, x j = i → t i j ≤ tt j) :
    -gT x (corr i x t tt) ≤ -gT x (corrStar x t) := by sorry

end AlgMechDesign.CompBonus
