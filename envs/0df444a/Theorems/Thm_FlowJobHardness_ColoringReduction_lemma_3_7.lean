-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_7
-- name    : FlowJobHardness.ColoringReduction.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:25.595618+00:00
-- url     : https://prove2.me/theorems/5b6edbf3-3343-4a94-8ed4-8429266a26f8
-- title:
--   Lemma 3.7 — an $L$-colourable graph gives a schedule of S(r, d) with makespan $\mathrm{lb}\cdot 2L$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r\in\mathbb N$, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb} = r^{2d}$.
--
--   If the vertices of $G$ can be coloured properly with $L$ colours, then $S(r,d)$ has a feasible schedule of all its jobs with makespan
--   $$
--   C_{\max} \le \mathrm{lb}\cdot 2L = 2L\, r^{2d}.
--   $$
--
--   This is the completeness half of the reduction: a graph of small chromatic number yields an instance with a short schedule.
--
--   **Formalization Note.** The paper's hypothesis $\chi(G) = L$ is stated as $L$-colourability (`G.Colorable L`), which is all the proof uses and includes the case $\chi(G)=L$. "A schedule with makespan $\mathrm{lb}\cdot 2L$" is read as makespan at most $2L\,r^{2d}$; the paper's own schedule ends at or before that time.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:17, Lemma 3.7

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Lemma 3.7** (Mastrolilli–Svensson 2011, p. 20:17). If `G` can be coloured with `L`
colours (`χ(G) = L` in the paper), then `S(r, d)` has a feasible schedule with makespan at most
`lb · 2L = 2L · r^{2d}`. -/
theorem lemma_3_7 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (L : ℕ) (hL : G.Colorable L) :
    ∃ s : (inst G c r).Op → ℝ,
      (inst G c r).IsFeasibleSchedule Finset.univ s ∧
      (inst G c r).makespan Finset.univ s ≤ 2 * (L : ℝ) * (R r d : ℝ) := by sorry

end FlowJobHardness.ColoringReduction
