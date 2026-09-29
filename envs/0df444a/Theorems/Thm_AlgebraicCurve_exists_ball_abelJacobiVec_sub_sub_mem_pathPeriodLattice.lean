-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
-- name    : AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2b57e9e2-273b-5cb2-8840-2bc5fa25a960
-- title:
--   Local holomorphic lift of the Abel–Jacobi vector
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, subject to the hypothesis `hfg` that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x) =$ `IntermediateField.adjoin ℂ {x}`, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place is $\mathrm{ord}_v(f)$, each residue field $v.\mathrm{ResidueField}$ is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$. The space `Place ℂ F` of places carries a topology, a charted space structure over $\mathbb{C}$ and an analytic manifold structure, and is assumed Hausdorff and connected; write $\varphi_v$ for the extended chart `extChartAt 𝓘(ℂ, ℂ) v` at a place $v$. The hypothesis `hF` requires that for every $f \neq 0$ and every place $v$ the function $z \mapsto$ `Place.evalAt` $(\varphi_v^{-1}(z))\,f$ is meromorphic at $\varphi_v(v)$ with `meromorphicOrderAt` equal to $v.\mathrm{ord}\,f$. Let $n \in \mathbb{N}$ and $b : \mathrm{Fin}\,n \to \Omega[F/\mathbb{C}]$ with each $b_i$ in `regularDifferentials ℂ F`, that is, for every place $v$ there is $f$ in the valuation subring of $v$ with $b_i = f \cdot v.\mathrm{dCoord}$, where $v.\mathrm{dCoord} = D_{\mathbb{C}/F}$ of a uniformizer at $v$. Let $P_0, P$ be places. Then there is $r > 0$ such that the ball $D$ of radius $r$ about $\varphi_P(P)$ lies in the target of $\varphi_P$, together with functions $\Phi_i : \mathbb{C} \to \mathbb{C}$ ($i \in \mathrm{Fin}\,n$) such that for each $i$ and each $z \in D$, $\Phi_i$ has derivative `P.readDifferential (b i) z` at $z$ — the product of the chart-read of the coefficient of $b_i$ with the derivative of the chart-read of the coordinate function of $P$ — and such that for every $z \in D$ the vector $$\mathrm{AJ}(\varphi_P^{-1}(z)) - \mathrm{AJ}(P) - \bigl(\Phi_i(z) - \Phi_i(\varphi_P(P))\bigr)_i$$ lies in `pathPeriodLattice b`, the $\mathbb{Z}$-span of the vectors $(\text{pathIntegral }(b_i)\,\gamma)_i$ over all loops $\gamma$ at all places. Here $\mathrm{AJ}(Q) =$ `abelJacobiVec b P₀ Q` is the vector of path integrals of the $b_i$ along one chosen path from $P_0$ to $Q$ when such a path exists, and $0$ otherwise, each path integral being the difference of the endpoint values of a primitive of $b_i$ along the path when one exists, and $0$ otherwise.
--
--   This is the local holomorphy of the Abel–Jacobi map on a coordinate disc: modulo the lattice of loop periods, the multivalued map $Q \mapsto \int_{P_0}^{Q} b$ admits in a local coordinate a single-valued primitive whose derivative is the local coefficient vector of $b$. It is the local input for Abel's theorem and for the behaviour of the Abel–Jacobi map on fibres and on correspondences, and is cited by [`AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice), [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice) and [`AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ Φ : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (Φ i) (P.readDifferential (b i) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiVec b P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec b P₀ P -
              (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by sorry
