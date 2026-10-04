-- Prove2me | Theorems.Thm_AnosovPlugs_contDiffOn_fixedPoint_of_contraction
-- name    : AnosovPlugs.contDiffOn_fixedPoint_of_contraction
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:36:24.84854+00:00
-- url     : https://prove2.me/theorems/d7e05020-8a7e-499b-965e-3ce92bab6588
-- title:
--   The fixed point of a C¹ family of contractions of a Banach space is a C¹ function of the parameter
-- statement:
--   Let $P$ and $B$ be real Banach spaces, let $U\subseteq P$ be open, and let $T:P\times B\to B$ be a map of class C¹. Assume that for every $p\in U$ the map $T_p=T(p,\cdot):B\to B$ is a contraction: there is $K_p<1$ with $\|T_p(b)-T_p(b')\|\le K_p\|b-b'\|$ for all $b,b'\in B$. Let $\mathrm{fp}:P\to B$ be a map such that $\mathrm{fp}(p)$ is the fixed point of $T_p$ for every $p\in U$. Then
--   $$ \mathrm{fp} \text{ is of class } C^1 \text{ on } U. $$
--
--   In words: the fixed point of a C¹ family of contractions depends in a C¹ way on the parameter. The contraction constant may depend on $p$ and need not be uniformly smaller than 1 on $U$. A general fact of analysis, not stated in the paper. In this mission it is a step in the proof of the companion theorem `exists_localFlow_contMDiff_of_isInteriorPoint`. That theorem says that the local flow of a C¹ vector field at an interior point is jointly C¹ in the initial point and the time. The proof of Proposition 1.1 (Section 3.1 of arXiv v1) uses it tacitly. There $P=E\times\mathbb R$ is the space of initial points and time scales, $B$ is a space of continuous curves, and $T$ is the Picard operator.
--
--   **Formalization Note** $T$ is curried in Lean (`T : P → B → B`), and the C¹ hypothesis is on the uncurried map `fun q : P × B => T q.1 q.2`. The fixed-point map `fp` is an arbitrary function with `T p (fp p) = fp p` for `p ∈ U`; it is unique there because each `T p` is a contraction. C¹ on $U$ is Mathlib's `ContDiffOn ℝ 1 fp U`. The expected proof applies the C¹ implicit function theorem (`ContDiffAt.implicitFunction` in Mathlib) to $(p,b)\mapsto b-T(p,b)$; the partial derivative in $b$ is the identity minus an operator of norm at most $K_p<1$, which is invertible.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1). General fact of analysis (implicit function theorem for a family of contractions), not stated in the paper; used tacitly in the proof of Proposition 1.1 through differentiable dependence of flows on initial conditions. Mathlib notions: ContDiff, ContDiffOn, LipschitzWith, ContDiffAt.implicitFunction.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem contDiffOn_fixedPoint_of_contraction
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (T : P → B → B) (hT : ContDiff ℝ 1 (fun q : P × B => T q.1 q.2))
    (U : Set P) (hU : IsOpen U)
    (hlip : ∀ p ∈ U, ∃ K : NNReal, K < 1 ∧ LipschitzWith K (T p))
    (fp : P → B) (hfp : ∀ p ∈ U, T p (fp p) = fp p) :
    ContDiffOn ℝ 1 fp U := by sorry

end AnosovPlugs
