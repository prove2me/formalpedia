-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_9
-- name    : FlowJobHardness.ColoringReduction.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:43.345987+00:00
-- url     : https://prove2.me/theorems/68aaa3d5-5b55-44fa-951d-152293d6c69f
-- title:
--   Lemma 3.9 — if half the jobs of S(r, d) finish by $\mathrm{lb}\cdot L$, then G has an independent set of size $n/(8L)$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r\ge 8$ be an integer, let $L$ be a real number with $0 < L \le r$, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb}=r^{2d}$.
--
--   If $S(r,d)$ has a feasible schedule in which at least half of its $r^{2d}n$ jobs finish within $\mathrm{lb}\cdot L$ time units, then $G$ has an independent set $I$ with
--   $$
--   |I| \ \ge\ \frac{n}{8L}.
--   $$
--
--   This is the soundness half of the reduction: a schedule in which many jobs finish early certifies a large independent set.
--
--   **Formalization Note.** The paper states that such an independent set can be found "in time polynomial in $n$ and $r^d$"; the algorithmic clause is not formalized, only the existence of the independent set. "At least half the jobs" is $2\cdot\#\{j : C_j \le L\,r^{2d}\} \ge r^{2d}n$. The paper's "for any $L \le r$" is taken with $L>0$, so that $n/(8L)$ is meaningful; for $L<1$ the hypothesis can only hold when $n=0$, since every job has length $r^{2d}$. The threshold $r \ge 8$ is inherited from Lemma 3.12.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:18, Lemma 3.9

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Lemma 3.9** (Mastrolilli–Svensson 2011, p. 20:18), mathematical content. Let `r ≥ 8`
and `0 < L ≤ r`. If `S(r, d)` has a feasible schedule in which at least half of the
`r^{2d} n` jobs finish within `lb · L = L · r^{2d}` time units, then `G` has an independent set
of size at least `n / (8L)`. (The paper's "in time polynomial in `n` and `r^d`" is not
formalized.) -/
theorem lemma_3_9 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (hLr : L ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (hhalf : (size r d n : ℝ) ≤ 2 * (finishedCount G c r s L : ℝ)) :
    ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧
      (n : ℝ) / (8 * L) ≤ (I.card : ℝ) := by sorry

end FlowJobHardness.ColoringReduction
