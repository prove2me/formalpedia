-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_10
-- name    : FlowJobHardness.ColoringReduction.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:44.041104+00:00
-- url     : https://prove2.me/theorems/fe26b252-10f0-4086-a1b4-d81de9fabd96
-- title:
--   Lemma 3.10 — a job finishing by $r\cdot\mathrm{lb}$ has a fraction at least $1-4/r$ of good long-operations
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r \ge 1$ be an integer, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb}=r^{2d}$. Fix a feasible schedule of all jobs.
--
--   Let $j$ be a job of frequency $f$, so $j$ has $r^{2f}$ long-operations, each of length $r^{2(d-f)}$. If the completion time of $j$ is at most $r\cdot\mathrm{lb}$, then the number of good long-operations of $j$ (those followed by the next long-operation of $j$ within delay $\tfrac{r^2}{4}r^{2(d-f)}$) satisfies
--   $$
--   \#\{\text{good long-operations of } j\} \ \ge\ \Big(1-\frac{4}{r}\Big)\, r^{2f}.
--   $$
--
--   In the paper this is applied to the jobs that finish within $L\cdot \mathrm{lb} \le r\cdot\mathrm{lb}$. It is the analogue for $S(r,d)$ of Lemma 2.2 for the flow shop gap instance.
--
--   **Formalization Note.** The paper's context ("all jobs (that were not disregarded) have completion time at most $L\cdot\mathrm{lb}$, which is by assumption at most $r\cdot\mathrm{lb}$") becomes the hypothesis $C_j \le r\cdot r^{2d}$ on the single job $j$. The fraction is stated as a count, multiplied out by the number $r^{2f}$ of long-operations of $j$.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:18, Lemma 3.10 (with the definition of good long-operations, p. 20:10)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Lemma 3.10** (Mastrolilli–Svensson 2011, p. 20:18). For `r ≥ 1`, in a feasible schedule
of `S(r, d)`, every job `q` of frequency `f` whose completion time is at most `r · lb =
r · r^{2d}` has at least `(1 - 4/r) · r^{2f}` good long-operations, i.e. a fraction at least
`1 - 4/r` of its `r^{2f}` long-operations is good. -/
theorem lemma_3_10 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 1 ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d n)) (hq : jobCompletion G c r s q ≤ (r : ℝ) * (R r d : ℝ)) :
    (1 - 4 / (r : ℝ)) * (r : ℝ) ^ (2 * jobFreq c q) ≤ (goodCount G c r s q : ℝ) := by sorry

end FlowJobHardness.ColoringReduction
