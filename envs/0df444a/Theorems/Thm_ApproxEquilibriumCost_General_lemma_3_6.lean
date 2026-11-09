-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_lemma_3_6
-- name    : ApproxEquilibriumCost.General.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:07.605374+00:00
-- url     : https://prove2.me/theorems/b8311434-73bc-4861-a13b-145a2636e468
-- title:
--   Lemma 3.6 — all analytic properties of μ and its unique cost minimizer
-- statement:
--   For every integer $d\ge1$, $\mu_d$ is continuous, strictly increasing and convex on $[0,1]$, and
--
--   $$\mu_d([0,1])=[0,1].$$
--
--   With $F_d(u)=1-u+\mu_d(u)$ and $b_d=d/(d+1)$, $F_d$ is decreasing on $[0,b_d]$ and increasing on $[b_d,1]$. Its minimum on $[0,1]$ is attained uniquely at $b_d$:
--
--   $$F_d(b_d)\le F_d(u),\qquad F_d(u)=F_d(b_d)\Longrightarrow u=b_d\quad(0\le u\le1).$$
--
--   All properties include the endpoints. The monotonicity clauses use weak order, together with the printed unique-minimizer clause. This is the analytic interface for the polynomial congestion bound.
--
--   Differences from the source:
--   - encoding: integer d ≥ 1 and the power (1−x)^(1/d) → natural d with 1 ≤ d and Real.rpow with real reciprocal; reason: the admissible degrees and all endpoint values are identical
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Lemma 3.6 (proof Appendix A, printed/PDF p.27), printed p.11 = PDF p.11 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Parameters

namespace ApproxEquilibriumCost.General

/-- Lemma 3.6, printed/PDF p.11; proof p.27. Includes every analytic
property and the unique attained minimum. -/
theorem lemma_3_6 (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (mu d) (Set.Icc 0 1) ∧
    StrictMonoOn (mu d) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1) (mu d) ∧
    mu d '' Set.Icc 0 1 = Set.Icc 0 1 ∧
    AntitoneOn (fun x => 1 - x + mu d x) (Set.Icc 0 (criticalPoint d)) ∧
    MonotoneOn (fun x => 1 - x + mu d x) (Set.Icc (criticalPoint d) 1) ∧
    criticalPoint d ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 - criticalPoint d + mu d (criticalPoint d) ≤ 1 - x + mu d x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 - x + mu d x = 1 - criticalPoint d + mu d (criticalPoint d) →
        x = criticalPoint d) := by sorry

end ApproxEquilibriumCost.General
