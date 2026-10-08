-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_remark_3_6
-- name    : FlowJobHardness.ColoringReduction.remark_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:23.944156+00:00
-- url     : https://prove2.me/theorems/4408adcb-4ed6-4ba4-b905-1c3625f4dedc
-- title:
--   Remark 3.6 — in S(r, d) every job length and every machine load is $r^{2d}$, and a job has at most $(\Delta+1)r^{2d}$ operations
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r\in\mathbb N$, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $r^{2d}n$ machines and $r^{2d}n$ jobs. Then:
--
--   1. every job has length (total processing time) $r^{2d}$;
--   2. every machine has load (total processing time of the operations assigned to it) $r^{2d}$;
--   3. if every vertex of $G$ has degree at most $\Delta$, then every job has at most $(\Delta+1)\,r^{2d}$ operations.
--
--   $$
--   \ell_j = r^{2d}, \qquad P_m = r^{2d}, \qquad \mu_j \le (\Delta+1)\, r^{2d}.
--   $$
--
--   Consequently the trivial lower bound $\mathrm{lb} = \max(\max_j \ell_j, \max_m P_m)$ on the optimal makespan equals $r^{2d}$, the unit in which all bounds of the reduction are expressed.
--
--   **Formalization Note.** The machine and job counts are definitional (both types are `Fin (r^{2d} n)`), so only the three listed properties are stated. The degree bound $\Delta$ is a hypothesis $\deg(v)\le\Delta$ for all $v$ rather than the maximum degree itself, which makes the statement apply to every upper bound. The section introduction (p. 20:12) states the weaker count "at most $d\,r^{2d}$ operations"; the two agree when $d = \Delta+1$, as in the proof of Theorem 1.2.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:17, Remark 3.6

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Remark 3.6** (Mastrolilli–Svensson 2011, p. 20:17). In `S(r, d)` (which has `r^{2d} n`
machines and `r^{2d} n` jobs by construction) every job has length `r^{2d}`, every machine has
load `r^{2d}`, and if every vertex of `G` has degree at most `Δ` then every job has at most
`(Δ + 1) r^{2d}` operations. -/
theorem remark_3_6 {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : G.Coloring (Fin d)) (r : ℕ) :
    (∀ q : Fin (size r d n), (inst G c r).jobLength q = (R r d : ℝ)) ∧
    (∀ p : Fin (size r d n), (inst G c r).load p = (R r d : ℝ)) ∧
    (∀ Δ : ℕ, (∀ v : Fin n, G.degree v ≤ Δ) →
      ∀ q : Fin (size r d n), (inst G c r).μ q ≤ (Δ + 1) * R r d) := by sorry

end FlowJobHardness.ColoringReduction
