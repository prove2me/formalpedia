-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_optimality_corrStar
-- name    : AlgMechDesign.CompBonus.optimality_corrStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:13:44.465026+00:00
-- url     : https://prove2.me/theorems/c130e686-e1b3-4315-8d50-22f762b5c482
-- title:
--   Claim 5.2, proof — the truthful corrected make-span is optimal
-- statement:
--   Let $x(\cdot)$ be an optimal allocation algorithm. Let $t = (d^{-i}, t^i)$ be a positive type vector in which agent $i$ has its true type $t^i$ and the others their declarations $d^{-i}$, and let $t'^i$ be any positive declaration of agent $i$. Then
--   $$
--   -g\big(x(t), \mathrm{corr}^*(x(t), t)\big) \;\ge\; -g\big(x(t'^i, d^{-i}), \mathrm{corr}^*(x(t'^i, d^{-i}), t)\big).
--   $$
--
--   Since $\mathrm{corr}^*(y, t)$ lists each task at the time its assigned agent needs under $t$, both sides are make-spans $-g(\cdot, t)$ of allocations under the same type vector, and the inequality says that a misreport by agent $i$ cannot produce an allocation that is better for $t$ than the optimal one. It is the displayed inequality to which the proof of Claim 5.2 reduces truthfulness.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, proof of Claim 5.2, first paragraph, displayed inequality in the third sentence and the fourth sentence

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- The displayed inequality in the proof of Claim 5.2 (p. 188): for an optimal allocation
algorithm `alloc`, a positive profile `t = (d⁻ⁱ, tⁱ)` and every positive declaration `ti'` of
agent `i`,
`-g(x(t), corr*(x(t), t)) ≥ -g(x(ti', d⁻ⁱ), corr*(x(ti', d⁻ⁱ), t))`. -/
theorem optimality_corrStar {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) (ti' : Fin k → ℝ)
    (hti' : IsAgentType ti') :
    -gT (alloc (Function.update t i ti')) (corrStar (alloc (Function.update t i ti')) t) ≤
      -gT (alloc t) (corrStar (alloc t) t) := by sorry

end AlgMechDesign.CompBonus
