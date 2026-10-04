-- Prove2me | Theorems.Thm_AnosovPlugs_exists_flow_contDiffOn_of_lipschitz
-- name    : AnosovPlugs.exists_flow_contDiffOn_of_lipschitz
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:36:44.859982+00:00
-- url     : https://prove2.me/theorems/ea27ea04-a010-45d1-a507-455482c75854
-- title:
--   The flow of a globally Lipschitz C¹ vector field on a Banach space is jointly C¹ in the initial point and the time
-- statement:
--   Let $E$ be a real Banach space and let $v:E\to E$ be a vector field of class C¹ that is globally Lipschitz with constant $K$. Then there are $\varepsilon>0$ and a map $\alpha:E\to\mathbb R\to E$ such that:
--   1. $\alpha(x,0)=x$ for every $x\in E$;
--   2. for every $x\in E$ and every $t\in(-\varepsilon,\varepsilon)$, the curve $\alpha(x,\cdot)$ is differentiable at $t$ with
--      $$ \frac{d}{dt}\alpha(x,t)=v(\alpha(x,t)); $$
--   3. the map $(x,t)\mapsto\alpha(x,t)$ is of class C¹ on $E\times(-\varepsilon,\varepsilon)$.
--
--   In words: the flow of a globally Lipschitz C¹ vector field on a Banach space is jointly C¹ in the initial point and the time, for a short time that does not depend on the initial point (differentiable dependence on initial conditions; for the finite-dimensional case see Hartman, *Ordinary Differential Equations*, Chapter V). A general fact of analysis, not stated in the paper. In this mission it is a step in the proof of the companion theorem `exists_localFlow_contMDiff_of_isInteriorPoint`. That theorem says that the local flow of a C¹ vector field at an interior point is jointly C¹ in the initial point and the time. The proof of Proposition 1.1 (Section 3.1 of arXiv v1) uses it tacitly. There it is applied to a cut-off of the vector field read in a chart.
--
--   **Formalization Note** Clause 3 is `ContDiffOn ℝ 1 (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε)`. The statement asks only for a short time interval; the expected proof takes $\varepsilon=1/(K+1)$, solves the rescaled integral equation $\beta(s)=x+\tau\int_0^s v(\beta)$ on a fixed interval by the contraction principle, and gets the regularity in $(x,\tau)$ from the companion theorems `contDiffOn_fixedPoint_of_contraction` and `contDiff_continuousMap_comp_left`. Mathlib (at the pinned version) has a Lipschitz estimate in the initial point and joint continuity of the local flow, but no differentiable dependence on initial conditions.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). Textbook ODE theory (differentiable dependence on initial conditions; for the finite-dimensional case see Hartman, Ordinary Differential Equations, Ch. V), not stated in the paper; used tacitly in the proof of Proposition 1.1. Mathlib notions: ContDiff, ContDiffOn, LipschitzWith, HasDerivAt; companion theorems contDiffOn_fixedPoint_of_contraction, contDiff_continuousMap_comp_left.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_flow_contDiffOn_of_lipschitz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : E → E) (hv : ContDiff ℝ 1 v) (K : NNReal) (hK : LipschitzWith K v) :
    ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, (∀ x, α x 0 = x) ∧
      (∀ x, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (v (α x t)) t) ∧
      ContDiffOn ℝ 1 (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε) := by sorry

end AnosovPlugs
