-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_claim_3_8
-- name    : FlowJobHardness.ColoringReduction.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:33.491269+00:00
-- url     : https://prove2.me/theorems/039bf317-376c-4055-bf80-b7d592a1cfeb
-- title:
--   Claim 3.8 — the jobs of an independent set can be scheduled within $2\cdot\mathrm{lb}$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r\in\mathbb N$, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb} = r^{2d}$. For a vertex $v$ let $J^v$ be the set of the $r^{2d}$ jobs of $v$.
--
--   If $IS \subseteq V$ is an independent set of $G$, then the jobs $\bigcup_{v\in IS} J^v$ admit a feasible schedule (nonnegative start times, the operations of each job in order, and no two operations overlapping on a machine) whose makespan satisfies
--   $$
--   C_{\max}\Big(\textstyle\bigcup_{v\in IS} J^v\Big) \le 2\cdot r^{2d}.
--   $$
--
--   This is the building block of the completeness direction: a colouring with $L$ colours splits the jobs into $L$ such blocks.
--
--   **Formalization Note.** The published model's feasibility and makespan are taken relative to the job subset $\{q : \text{vertex}(q) \in IS\}$; operations of the other jobs are ignored. "Scheduled within $2\cdot\mathrm{lb}$ time units" is read as makespan $\le 2\,r^{2d}$.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:17, Claim 3.8

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Claim 3.8** (Mastrolilli–Svensson 2011, p. 20:17). If `IS` is an independent set of `G`,
then the jobs `⋃_{v ∈ IS} J^v` of `S(r, d)` have a feasible schedule with makespan at most
`2 · lb = 2 r^{2d}`. -/
theorem claim_3_8 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (IS : Finset (Fin n)) (hIS : G.IsIndepSet (IS : Set (Fin n))) :
    ∃ s : (inst G c r).Op → ℝ,
      (inst G c r).IsFeasibleSchedule
        (Finset.univ.filter fun q : Fin (size r d n) => jobVtx q ∈ IS) s ∧
      (inst G c r).makespan
        (Finset.univ.filter fun q : Fin (size r d n) => jobVtx q ∈ IS) s ≤
        2 * (R r d : ℝ) := by sorry

end FlowJobHardness.ColoringReduction
