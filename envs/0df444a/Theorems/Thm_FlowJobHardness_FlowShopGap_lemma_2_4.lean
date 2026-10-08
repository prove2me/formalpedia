-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_lemma_2_4
-- name    : FlowJobHardness.FlowShopGap.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:41.275095+00:00
-- url     : https://prove2.me/theorems/9aeca8dd-4015-42f0-b5f9-d2261722e5e7
-- title:
--   Lemma 2.4 — some machine group $g$ has $\sum_{f=1}^d L(T_{g,f})\ge(\mathrm{lb}/4)\cdot d$
-- statement:
--   Let $r\ge8$ and $d$ be natural numbers and let $s$ be a feasible schedule of the flow shop instance $F(r,d)$ whose makespan is less than $r\cdot\mathrm{lb}=r\cdot r^{2d}$. Then there is a machine group $g\in\{1,\dots,r^{2d}\}$ such that
--   $$\sum_{f=1}^{d} L(T_{g,f})\ \ge\ \frac{\mathrm{lb}}{4}\cdot d=\frac{r^{2d}}{4}\cdot d ,$$
--   where $L(T_{g,f})$ is the total time covered by the first halves of the good long-operations on machine $m_{g,f}$.
--
--   With Lemma 2.3, this gives a single machine group whose first-half intervals are pairwise disjoint and have total length at least $\mathrm{lb}\cdot d/4$, which yields the lower bound of the main theorem.
--
--   **Formalization Note** The paper states Lemma 2.4 under the standing assumption of §2.2.2 (p. 20:10) that the schedule's makespan is less than $r\cdot\mathrm{lb}$; it is an explicit hypothesis here. "For a sufficiently large $r$" in the proof stands for $1-4/r\ge1/2$, i.e. $r\ge8$.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:11, Lemma 2.4 (standing assumption on p. 20:10)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-- Lemma 2.4 (p. 20:11), under the standing assumption of §2.2.2 that the makespan is less
than `r · lb`: for `r ≥ 8` and every feasible schedule of `F(r, d)` with makespan
`< r · r^{2d}`, some machine group `g ∈ {1, …, r^{2d}}` has
`∑_{f=1}^{d} L(T_{g,f}) ≥ (lb/4) · d`. -/
theorem lemma_2_4 (r d : ℕ) (hr : 8 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (hmk : (inst r d).makespan Finset.univ s < (r : ℝ) * (r : ℝ) ^ (2 * d)) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ r ^ (2 * d) ∧
      (r : ℝ) ^ (2 * d) / 4 * (d : ℝ) ≤ ∑ f ∈ Finset.Icc 1 d, L r d s g f := by sorry

end FlowJobHardness.FlowShopGap
