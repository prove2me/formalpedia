-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_proposition_3_7_strong
-- name    : ClosedLoopMFG.Converse.proposition_3_7_strong
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:19.217276+00:00
-- url     : https://prove2.me/theorems/777b482d-fab8-4dea-bd24-cdb95bec909f
-- title:
--   Proposition 3.7 (strong part) — under convexity, strong MFE and strong relaxed MFE are the same flows
-- statement:
--   Suppose Assumptions A and B hold. Let $m\in C([0,T];\mathcal P(\mathbb R^d))$. Then
--   $$m\ \text{is a strong MFE}\iff m\ \text{is a strong RMFE}.$$
--   In words: every strong relaxed mean field equilibrium is a strong mean field equilibrium, and every strong mean field equilibrium is a strong relaxed mean field equilibrium.
--
--   This is the bridge from strict to relaxed controls in the mean field game. Theorem 2.11 uses the direction "strong MFE $\Rightarrow$ strong RMFE" to reduce to Theorem 3.10.
--
--   **Formalization Note** The paper's Proposition 3.7 also has a weak part (weak RMFE versus weak MFE), which is not posed in this mission. The printed "strong RFME" is a typo for strong RMFE. $T>0$ is the paper's standing assumption.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 17, Proposition 3.7 (strong part)

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem proposition_3_7_strong {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ) (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    (m : Flow d T) :
    IsStrongMFE T A lam b f g m ↔ IsStrongRMFE T A lam b f g m := by sorry

end ClosedLoopMFG.Converse
