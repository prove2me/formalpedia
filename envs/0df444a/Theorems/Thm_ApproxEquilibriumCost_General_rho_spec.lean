-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_rho_spec
-- name    : ApproxEquilibriumCost.General.rho_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:23.79582+00:00
-- url     : https://prove2.me/theorems/cab007ac-6103-4e73-9344-b369f20abf6f
-- title:
--   Definition 3.1 — range, root equation and uniqueness of the constructed ρ
-- statement:
--   For every integer $d\ge1$ and every real $\epsilon\ge0$, the canonically constructed $\rho_d(\epsilon)$ satisfies
--
--   $$0\le\rho_d(\epsilon)<1,\qquad\mu_d(\rho_d(\epsilon))=\epsilon(1-\rho_d(\epsilon)).$$
--
--   Every $u\in[0,1)$ satisfying the same equation equals $\rho_d(\epsilon)$. This item records the assertion accompanying Definition 3.1 as an auxiliary interface obligation. It is not an additional source-numbered milestone, and the goal does not take the equation or uniqueness as hypotheses.
--
--   Differences from the source:
--   - encoding: integer d ≥ 1 and the power (1−x)^(1/d) → natural d with 1 ≤ d and Real.rpow with real reciprocal; reason: the admissible degrees and all endpoint values are identical
--   - encoding: ρ_d(ε) is the unique root of μ_d(u)=ε(1−u) in [0,1) → ρ_d(ε) is the infimum of {u∈[0,1] : ε(1−u)≤μ_d(u)}, with zero outside d≥1, ε≥0; reason: continuity and strict increase identify this nonempty bounded infimum with the unique source root; outside-domain defaults never enter a source-domain theorem
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Definition 3.1, paragraph defining ρ, printed p.10 = PDF p.10 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Parameters

namespace ApproxEquilibriumCost.General

/-- Definition 3.1, p.10: the infimum construction is the unique root
specified by the source. Auxiliary interface obligation, not a numbered milestone. -/
theorem rho_spec (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    rho d ε ∈ Set.Ico (0 : ℝ) 1 ∧
    mu d (rho d ε) = ε * (1 - rho d ε) ∧
    (∀ x ∈ Set.Ico (0 : ℝ) 1, mu d x = ε * (1 - x) → x = rho d ε) := by sorry

end ApproxEquilibriumCost.General
