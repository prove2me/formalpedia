-- Prove2me | Theorems.Thm_FlowJobHardness_FlowShopGap_lemma_2_2
-- name    : FlowJobHardness.FlowShopGap.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:52.858953+00:00
-- url     : https://prove2.me/theorems/f49c3367-c342-46cc-9b2b-cd2f8f4c7037
-- title:
--   Lemma 2.2 — below makespan $r\cdot\mathrm{lb}$, at least a $(1-4/r)$ fraction of each job's long-operations are good
-- statement:
--   Let $r\ge 1$ and $d$ be natural numbers and let $s$ be a feasible schedule of the flow shop instance $F(r,d)$ (nonnegative start times, the operations of each job in order, no two operations on one machine overlapping). Suppose the makespan of $s$ is less than $r\cdot\mathrm{lb}=r\cdot r^{2d}$. Then for every job $j$,
--   $$\#\{\text{good long-operations of } j\}\ \ge\ \Bigl(1-\frac4r\Bigr)\cdot\#\{\text{long-operations of } j\}.$$
--   (A job of frequency $f$ has $r^{2f}$ long-operations.)
--
--   This lemma converts the assumption "the makespan is small" into the statement that most long-operations of every job are followed quickly by the next one; it feeds the averaging argument of Lemma 2.4.
--
--   **Formalization Note** The paper states the lemma for "sufficiently large" $r$ without a threshold; the statement as formalized holds for every $r\ge1$ (for $r\le4$ the right-hand side is nonpositive). Fractions are compared as real numbers, after multiplying by the number of long-operations.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:10, Lemma 2.2

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-- Lemma 2.2 (p. 20:10): if a feasible schedule of `F(r, d)` has makespan less than
`r · lb = r · r^{2d}`, then for every job the fraction of its long-operations that are good is
at least `1 - 4/r`. -/
theorem lemma_2_2 (r d : ℕ) (hr : 1 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (hmk : (inst r d).makespan Finset.univ s < (r : ℝ) * (r : ℝ) ^ (2 * d))
    (q : Fin (size r d)) :
    (1 - 4 / (r : ℝ)) * (longCount r d q : ℝ) ≤ (goodCount r d s q : ℝ) := by sorry

end FlowJobHardness.FlowShopGap
