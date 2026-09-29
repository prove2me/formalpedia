-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
-- name    : AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/22be6bd5-c2e4-5032-9d4e-b8cdf67db0d6
-- title:
--   Fundamental cycles realised by loops in the skeleton
-- statement:
--   Let $F$ be a field of characteristic-zero type over $\mathbb{C}$ which is a curve over $\mathbb{C}$ (principal divisors, finite residue extensions, and $\Omega[F/\mathbb{C}]$ free of rank one) and essentially of finite type, and let its place set $\mathrm{Place}\,\mathbb{C}\,F$ carry a Hausdorff charted structure making it an analytic $\mathbb{C}$-manifold. Assume `hfg`: some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite over $\mathbb{C}(x)$; and `hF`: for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{evalAt}$ of $f$ at the point with chart coordinate $z$ is meromorphic at the chart image of $v$, with meromorphic order equal to $v.\mathrm{ord}\,f$. Let $\mathcal{D}$ be a cell dissection of $F$, with edge set $\iota E$, vertex set $\iota V$, `ends` assigning to each edge its (tail, head) pair and `vert` realising vertices as places. Let $\mathcal{T}$ be a finite set of edges and $Z : \iota E \to \iota E \to \mathbb{Z}$, subject to: each $Z j$ satisfies Kirchhoff's law at every vertex $w$ (the sum of $Z j e$ over edges with head $w$ equals the sum over edges with tail $w$); $Z j j' = \delta_{jj'}$ for $j, j'$ outside $\mathcal{T}$; $Z j = 0$ for $j \in \mathcal{T}$; for all vertices $u, v$ there is exactly one integer chain supported on $\mathcal{T}$ whose boundary (head-sums minus tail-sums) is $\delta_v - \delta_u$; and any two vertices are joined by a walk along edges of $\mathcal{T}$ traversed in either direction. Then for each edge $j$ there exists a loop $\gamma$ at the place $\mathcal{D}.\mathrm{vert}$ of the tail of $j$, with $\gamma(t)$ lying in the skeleton $\mathcal{D}.\mathrm{skeleton}$ (the union over all cell-and-side pairs of the corresponding closed boundary arcs) for all $t$, such that every $\theta \in \Omega[F/\mathbb{C}]$ whose differential order $\mathrm{ord}(x.\mathrm{differentialCoeff}\,\theta)$ is non-negative at every point $x$ of the skeleton admits a primitive along $\gamma$ in the sense of `IsPrimitiveAlong`, and $\mathrm{pathIntegral}\,\theta\,\gamma = \sum_e Z j e \cdot \mathcal{D}.\mathrm{edgeInt}\,\theta\,e$, the edge integrals being the integrals of the cell boundary integrand over the parameter interval of the positively oriented arc representing $e$.
--
--   This is the topological input converting the fundamental cycles of a spanning tree in the one-skeleton of a cell dissection into actual loops on the Riemann surface of places, along which a differential regular on the skeleton has a well-defined period expressed as an integer combination of edge integrals. It feeds the reciprocity statement for path integrals of differentials over such loops, [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (𝒟 : CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZk : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e)
    (hZd : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0)
    (hZ0 : ∀ j ∈ 𝒯, Z j = 0)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    (j : 𝒟.ιE) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ 𝒟.skeleton) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * 𝒟.edgeInt θ e := by sorry
