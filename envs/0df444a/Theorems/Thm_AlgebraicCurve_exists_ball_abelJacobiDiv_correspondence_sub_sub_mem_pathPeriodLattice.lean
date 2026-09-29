-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
-- name    : AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b090f7b4-2646-5bb9-aba6-fa490dffe678
-- title:
--   Local holomorphic lift of AJ∘ T modulo periods
-- statement:
--   Let $F$ be a field which is an algebra over $\mathbb C$, assumed (hypothesis `hfg`) to contain an element $x$ transcendental over $\mathbb C$ with $F$ finite-dimensional over the intermediate field $\mathbb C(x)$, and assumed to satisfy `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor of degree $0$ recording the orders $\operatorname{ord}_v f$, each place has residue field finite over $\mathbb C$, and $\Omega[F/\mathbb C]$ is free of rank one over $F$. The set $\mathrm{Place}\ \mathbb C\ F$ of places carries a topology, a charted structure over $\mathbb C$ making it an analytic manifold, and is compact, Hausdorff and connected; the hypothesis `hF` says that for every nonzero $f \in F$ and every place $v$ the function $z \mapsto \mathrm{evalAt}\,((\mathrm{extChartAt}\ v)^{-1} z)\, f$ is meromorphic at $\mathrm{extChartAt}\ v\ v$ with `meromorphicOrderAt` equal to $\operatorname{ord}_v f$. Let $F'$ be a field, an algebra over $\mathbb C$ in which every nonzero element has a degree-zero divisor, let $\varphi, \psi : F \to F'$ be $\mathbb C$-algebra maps whose underlying ring homomorphisms are integral, and assume `FiniteAlong ℂ ψ`, i.e. $F'$ is a finite module over $F$ via $\psi$. Let $b_1,\dots,b_n \in \Omega[F/\mathbb C]$ be regular differentials (at each place $v$, $b_i = f\cdot v.\mathrm{dCoord}$ for some $f$ in the valuation subring of $v$), and let $P_0, P$ be places. The assertion is that there exists $r > 0$ such that the ball of radius $r$ about $\mathrm{extChartAt}\ P\ P$ lies in the target of the extended chart at $P$, together with functions $G_1,\dots,G_n : \mathbb C \to \mathbb C$, such that for each $i$ and each $z$ in that ball $G_i$ has derivative at $z$ equal to $P.\mathrm{readDifferential}$ of $\mathrm{tr}_\varphi(\psi^* b_i)$ at $z$ (that is, the chart reading of the coefficient of that differential times the derivative of the chart reading of the local coordinate `dCoordFn`), and such that for every $z$ in the ball the vector $$\mathrm{AJ}\bigl(\psi_*\varphi^*[(\mathrm{extChartAt}\ P)^{-1} z]\bigr) - \mathrm{AJ}\bigl(\psi_*\varphi^*[P]\bigr) - \bigl(G_i(z) - G_i(\mathrm{extChartAt}\ P\ P)\bigr)_i$$ lies in `pathPeriodLattice b`, the $\mathbb Z$-span of the vectors $(\oint_\gamma b_i)_i$ over closed paths $\gamma$ at places. Here $\mathrm{AJ} =$ `abelJacobiDiv b P₀` is the additive map on divisors sending $[v]$ to the vector of integrals `abelJacobiVec b P₀ v`, and the correspondence on divisors is the pushforward along $\psi$ composed after the pullback along $\varphi$.
--
--   This is the infinitesimal form of the classical statement that, modulo the period lattice, the composite of a correspondence with the Abel–Jacobi map is holomorphic on the Riemann surface of $F$, with differential the vector $(\mathrm{tr}_\varphi \psi^* b_i)_i$. It is used in [`AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice), where the local lift is globalised to identify the action of the correspondence on the Abel–Jacobi image with a matrix action modulo periods.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice.lean

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

theorem AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
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
    (F' : Type*) [Field F'] [Algebra ℂ F'] [HasPrincipalDivisors ℂ F']
    (φ ψ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ψ)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ G : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (G i) (P.readDifferential (Differential.correspondence φ ψ (b i)) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiDiv b P₀ (Divisor.correspondence φ ψ hφ hψ
                (Finsupp.single ((extChartAt 𝓘(ℂ, ℂ) P).symm z) 1)) -
              abelJacobiDiv b P₀ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)) -
              (fun i => G i z - G i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by sorry
