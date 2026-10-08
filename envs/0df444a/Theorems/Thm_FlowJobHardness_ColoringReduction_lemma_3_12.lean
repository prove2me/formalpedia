-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_12
-- name    : FlowJobHardness.ColoringReduction.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:30.866847+00:00
-- url     : https://prove2.me/theorems/da58ac64-5c5d-4b52-92da-eff09fa1dfcb
-- title:
--   Lemma 3.12 — some machine group has $\sum_v L(T_{g,v}) \ge \mathrm{lb}\cdot n/8$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes, let $r \ge 8$ be an integer, let $L$ be a real number with $0 < L \le r$, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction, with $\mathrm{lb} = r^{2d}$. Fix a feasible schedule of all jobs in which at least half of the $r^{2d}n$ jobs finish within $L\cdot\mathrm{lb}$, and let $T_{g,v}$ be the sets of first halves of good long-operations of those jobs on the machines $m_{g,v}$, with covered lengths $L(T_{g,v})$.
--
--   Then there is a group index $g\in\{1,\dots,r^{2d}\}$ such that
--   $$
--   \sum_{v\in V} L(T_{g,v}) \ \ge\ \frac{\mathrm{lb}\cdot n}{8}.
--   $$
--
--   This is the counting step of the soundness proof: a large amount of first-half time is concentrated in a single machine group.
--
--   **Formalization Note.** "At least half the jobs" is $2\cdot\#\{j : C_j \le L\,r^{2d}\} \ge r^{2d}n$. The paper proves the lemma "in the very same way as Lemma 2.4", whose last step uses $(1-4/r) > 1/2$ "for a sufficiently large $r$"; with the non-strict inequality $(1-4/r)\cdot\mathrm{lb}\cdot n/4 \ge \mathrm{lb}\cdot n/8$ the threshold is $r \ge 8$, which is the explicit hypothesis here.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:18, Lemma 3.12 (proved as Lemma 2.4, p. 20:11)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Lemma 3.12** (Mastrolilli–Svensson 2011, p. 20:18). Let `r ≥ 8` and `0 < L ≤ r`, and
let `s` be a feasible schedule of `S(r, d)` in which at least half of the `r^{2d} n` jobs
finish within `L · lb`. Then (keeping only those jobs in `T_{g,v}`) there is a group
`g ∈ {1, …, r^{2d}}` with `∑_{v ∈ V} L(T_{g,v}) ≥ lb · n / 8`. -/
theorem lemma_3_12 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (hLr : L ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (hhalf : (size r d n : ℝ) ≤ 2 * (finishedCount G c r s L : ℝ)) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ R r d ∧
      (R r d : ℝ) * n / 8 ≤ ∑ v : Fin n, coveredLength G c r s L g v := by sorry

end FlowJobHardness.ColoringReduction
