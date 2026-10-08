-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_lb_display
-- name    : FlowJobHardness.FlowShopGap.lb_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:01.085019+00:00
-- url     : https://prove2.me/theorems/3640b429-5437-4261-aeb7-59e25c6bc2d1
-- title:
--   §2.2.1 — in $F(r,d)$ every job length and every machine load equals $r^{2d}=\mathrm{lb}$
-- statement:
--   Let $F(r,d)$ be the flow shop instance of Section 2.2.1, with $r^{2d}\cdot d$ machines and $r^{2d}\cdot d$ jobs. Then every job has total processing time $r^{2d}$ and every machine has load $r^{2d}$:
--   $$\sum_{i} p_{ij}=r^{2d}\ \text{ for every job } j,\qquad \sum_{o \text{ on machine } t} p_o=r^{2d}\ \text{ for every machine } t .$$
--   Consequently the dilation $D$ (longest job) and the congestion $C$ (largest load) both equal $r^{2d}$, and the trivial lower bound $\mathrm{lb}=\max(C,D)$ on the optimal makespan is $r^{2d}$.
--
--   This identifies $\mathrm{lb}$ for the instance, which is what the main theorem compares the makespan of every schedule against.
--
--   **Formalization Note** The numbers of machines and of jobs, $r^{2d}d$, are built into the type `Fin (size r d)` and need no statement. No hypothesis on $r,d$ is needed: when $r=0$ or $d=0$ the instance has no jobs and no machines and the statement is vacuous.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:10, §2.2.1 ("Note that the length of any job and the load on any machine are r^{2d}, which equals lb.")

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-- §2.2.1, p. 20:10: in `F(r, d)` every job has length `r^{2d}` and every machine has load
`r^{2d}` (so `lb = r^{2d}`). The numbers of machines and of jobs, `r^{2d}·d`, are built into
the type `Fin (size r d)`. -/
theorem lb_display (r d : ℕ) :
    (∀ q : Fin (size r d), (inst r d).jobLength q = (r : ℝ) ^ (2 * d)) ∧
      (∀ t : Fin (size r d), (inst r d).load t = (r : ℝ) ^ (2 * d)) := by sorry

end FlowJobHardness.FlowShopGap
