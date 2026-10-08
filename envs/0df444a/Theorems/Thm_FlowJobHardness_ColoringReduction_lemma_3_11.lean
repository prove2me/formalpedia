-- Prove2me | Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_11
-- name    : FlowJobHardness.ColoringReduction.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:35.176187+00:00
-- url     : https://prove2.me/theorems/ad2aae31-76ec-411d-a7d7-17eb18c00451
-- title:
--   Lemma 3.11 — for adjacent vertices $u\in I_k$, $v\in I_l$, $k>l$, the interval sets $T_{g,u}$ and $T_{g,v}$ are disjoint
-- statement:
--   Let $G$ be a simple graph on $n$ vertices with a proper colouring into $d$ classes $I_1,\dots,I_d$, let $r \ge 2$ be an integer, and let $S(r,d)$ be the generalized flow shop instance of the colouring reduction. Fix a feasible schedule of all jobs and a threshold $L$; $T_{g,w}$ is the set of first halves of the good long-operations on machine $m_{g,w}$ of the jobs finishing within $L\cdot r^{2d}$.
--
--   Let $u \in I_k$ and $v \in I_l$ be adjacent vertices with $k > l$. Then for every group $g$ with $1 \le g \le r^{2d}$, every interval of $T_{g,u}$ is disjoint from every interval of $T_{g,v}$:
--   $$
--   \forall\, I \in T_{g,u},\ \forall\, J \in T_{g,v}: \quad I \cap J = \emptyset .
--   $$
--
--   Thus at any moment, among the first halves of good long-operations in one machine group, adjacent vertices are never active simultaneously. This is what turns a point of heavy overlap into an independent set.
--
--   **Formalization Note.** $u\in I_k$, $v\in I_l$ with $k>l$ is the hypothesis $f(v) < f(u)$ on the frequencies $f = c+1$. The paper states the lemma for "a schedule" in the context of Lemma 3.9; it is stated here for every feasible schedule and every threshold $L$. The bound $r \ge 2$ makes the paper's inequality $r^{2(d-l)}/2 - r^{2(d-k)} > \tfrac{r^2}{4}r^{2(d-k)}$ ("using $k>l$", p. 20:11, proof of Lemma 2.3) hold. The paper leaves it implicit, since it takes $r$ large.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:18, Lemma 3.11

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-- **Lemma 3.11** (Mastrolilli–Svensson 2011, p. 20:18). Let `r ≥ 2`, let `s` be a feasible
schedule of `S(r, d)`, and let `u ∈ I_k`, `v ∈ I_l` be adjacent vertices with `k > l`. Then for
every group `g` (and every threshold `L` defining which jobs are kept), every interval of
`T_{g,u}` is disjoint from every interval of `T_{g,v}`. -/
theorem lemma_3_11 {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 2 ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (u v : Fin n) (huv : G.Adj u v) (hfreq : freq c v < freq c u)
    (L : ℝ) (g : ℕ) (hg1 : 1 ≤ g) (hg2 : g ≤ R r d) :
    ∀ I ∈ T G c r s L g u, ∀ J ∈ T G c r s L g v, Disjoint I J := by sorry

end FlowJobHardness.ColoringReduction
