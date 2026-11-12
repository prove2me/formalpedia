-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_smith_rule
-- name    : FasterWCTFPTAS.Main.smith_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:36.096948+00:00
-- url     : https://prove2.me/theorems/acfff2d6-e0c2-4454-9192-96348abb29ee
-- title:
--   §4, Smith's rule [Smi56] — processing each machine's jobs by non-increasing w_j/p_j is optimal
-- statement:
--   Let $p_1,\dots,p_n>0$ be processing times and $w_1,\dots,w_n\ge0$ weights, and fix $m$ machines. For every assignment $\sigma$ of the jobs to the machines and every choice of an order of the jobs on each machine (given by a priority permutation $\rho$),
--
--   $$
--   \mathrm{smithCost}(\sigma)\le\mathrm{cost}(\sigma,\rho),
--   $$
--
--   where $\mathrm{smithCost}(\sigma)$ is the cost of $\sigma$ when every machine processes its jobs in non-increasing order of $w_j/p_j$, ties broken by index. Equivalently, for a sorted instance ($w_1/p_1\ge\dots\ge w_n/p_n$) an optimal order in which to schedule a set of jobs on one machine is by increasing index.
--
--   This is the reason §4 may describe a schedule by a partition of the jobs alone, and it identifies $\mathrm{OPT}$ with the minimum over Smith-ordered assignments.
--
--   Differences from the source:
--   - encoding: one machine and a set S ⊆ [n] of jobs: an optimal order is by increasing index → every assignment σ to m machines and every per-machine order ρ: smithCost σ ≤ cost σ ρ; reason: the cost of an assignment is the sum of the per-machine costs, so the per-machine statement and the statement for all assignments are equivalent
--   - generalization: instance sorted so that w_1/p_1 ≥ … ≥ w_n/p_n; order by increasing index → any instance; order by non-increasing w_j/p_j with ties by index (Smith's order); reason: on a sorted instance Smith's order with ties by index is the increasing-index order, so the statement specializes to the source's
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 11 (PDF p. 12), §4, Smith's rule (see [Smi56])

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- §4, p. 11 (PDF 12), Smith's rule [Smi56]: on every machine, processing the jobs in
non-increasing order of `w_j/p_j` (ties by index) is optimal. Stated for every assignment `σ` to
`m` machines and every per-machine order (induced by the priority permutation `ρ`): the Smith-order
cost of `σ` is at most the cost of `(σ, ρ)`. -/
theorem smith_rule {n m : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n) :
    smithCost p w σ ≤ cost p w σ ρ := by sorry

end FasterWCTFPTAS.Main
