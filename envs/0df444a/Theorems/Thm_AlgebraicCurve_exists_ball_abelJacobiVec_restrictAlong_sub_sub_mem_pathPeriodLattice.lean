-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
-- name    : AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9291f2c5-2903-5881-a835-c26c089c32af
-- title:
--   Local primitive for the Abel–Jacobi vector pulled back along ψ
-- statement:
--   Let $F$ be a field extension of $\mathbb{C}$ admitting an element $x$ transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$, satisfying `IsCurveOver ℂ F` (principal divisors, finite residue extensions at every place, and $\Omega[F/\mathbb{C}]$ free of rank one over $F$), and suppose the space `Place ℂ F` of places carries a topology, charts modelled on $\mathbb{C}$, an analytic manifold structure, and is compact, Hausdorff and connected; the hypothesis `hF` requires that for every $f \neq 0$ and every place $v$ the chart read $z \mapsto \mathrm{evalAt}\,((\mathrm{extChartAt}\ v)^{-1} z)\, f$ is meromorphic at the chart image of $v$ with meromorphic order equal to $v.\mathrm{ord}\,f$. Let $F'$ be a second such extension, with its own transcendence hypothesis `hfg'`, `IsCurveOver ℂ F'`, a Hausdorff charted topology on `Place ℂ F'`, and the analogous compatibility `hF'`. Let $\psi : F \to F'$ be a $\mathbb{C}$-algebra map whose underlying ring homomorphism is integral, let $b_1,\dots,b_n \in \Omega[F/\mathbb{C}]$ be regular, i.e. at each place $v$ of $F$ one has $b_i = f\cdot v.\mathrm{dCoord}$ with $f$ in the valuation subring of $v$, let $P_0$ be a place of $F$ and $W$ a place of $F'$. Then there is $r > 0$ such that the ball of radius $r$ about the chart image of $W$ lies in the target of the extended chart at $W$, together with functions $\Psi_1,\dots,\Psi_n : \mathbb{C} \to \mathbb{C}$ such that on that ball each $\Psi_i$ has derivative at every point $u$ equal to `W.readDifferential (Differential.pullbackAlong ψ (b i)) u`, the chart coefficient at $W$ of the pullback of $b_i$ along $\psi$; and for every $u$ in the ball the vector $$\mathrm{abelJacobiVec}\,b\,P_0\,\bigl(((\mathrm{extChartAt}\ W)^{-1}u).\mathrm{restrictAlong}\ \psi\bigr) - \mathrm{abelJacobiVec}\,b\,P_0\,(W.\mathrm{restrictAlong}\ \psi) - \bigl(\Psi_i(u) - \Psi_i(\mathrm{extChartAt}\ W\ W)\bigr)_i$$ lies in `pathPeriodLattice b`, the $\mathbb{Z}$-span of the vectors of path integrals $\bigl(\int_\gamma b_i\bigr)_i$ over closed paths $\gamma$ at places of $F$. Here $\mathrm{abelJacobiVec}$ is the vector of path integrals of the $b_i$ along a chosen path from $P_0$ (and is $0$ when no path exists), and $w.\mathrm{restrictAlong}\ \psi$ is the place of $F$ obtained by restricting $w$ along $\psi$.
--
--   This is the local holomorphy statement for the composite of the Abel–Jacobi map of $F$ with the map of places $w \mapsto w \cap F$ induced by an integral embedding $\psi : F \to F'$: modulo periods, that composite is locally a primitive of the chart reads of the pulled-back differentials $\psi^{*}b_i$. The case $\psi = \mathrm{id}$ is [`AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice), and the present result feeds the corresponding statement for the Abel–Jacobi image of divisors under a correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (F' : Type*) [Field F'] [Algebra ℂ F']
    (hfg' : ∃ y : F', Transcendental ℂ y ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({y} : Set F')) F')
    [IsCurveOver ℂ F']
    [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
    (hF' : ∀ f : F', f ≠ 0 → ∀ w : Place ℂ F',
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) = (w.ord f : WithTop ℤ))
    (ψ : F →ₐ[ℂ] F') (hψ : ψ.toRingHom.IsIntegral)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ : Place ℂ F) (W : Place ℂ F') :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r ⊆ (extChartAt 𝓘(ℂ, ℂ) W).target ∧
      ∃ Ψ : Fin n → ℂ → ℂ,
        (∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          HasDerivAt (Ψ i) (W.readDifferential (Differential.pullbackAlong ψ (b i)) u) u) ∧
        ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          abelJacobiVec b P₀ (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) -
              abelJacobiVec b P₀ (W.restrictAlong ψ hψ) -
              (fun i => Ψ i u - Ψ i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ pathPeriodLattice b := by sorry
