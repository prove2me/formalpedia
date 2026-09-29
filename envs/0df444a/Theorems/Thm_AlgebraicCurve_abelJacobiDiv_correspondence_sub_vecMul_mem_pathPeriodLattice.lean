-- Prove2me | Theorems.Thm_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
-- name    : AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/a5a7825b-f5bf-5c2a-9b58-082c2e954788
-- title:
--   Abel–Jacobi intertwines a correspondence with its differential matrix
-- statement:
--   Let $F$ be a field equipped with a $\mathbb C$-algebra structure such that some $x \in F$ is transcendental over $\mathbb C$ with $F$ finite-dimensional over $\mathbb C(x) = \mathbb C(\{x\})$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor with multiplicities $\operatorname{ord}_v f$ and degree $0$, all residue fields of places are finite over $\mathbb C$, and $\Omega[F/\mathbb C]$ is free of rank $1$ over $F$. Suppose the set of places `Place ℂ F` carries a compact, Hausdorff, connected charted space structure over $\mathbb C$ making it an analytic manifold, compatibly with $F$ in the sense of `hF`: for each nonzero $f$ and each place $v$, the function $z \mapsto$ `Place.evalAt` of $f$ at the place $(\text{extChartAt } v)^{-1} z$ is meromorphic at the chart image of $v$ with `meromorphicOrderAt` equal to $\operatorname{ord}_v f$. Let $F'$ be a field with a $\mathbb C$-algebra structure in which every nonzero element has a degree-zero divisor with the expected multiplicities, and let $\varphi, \psi : F \to F'$ be $\mathbb C$-algebra maps whose underlying ring homomorphisms are integral, with $F'$ finite as a module over $F$ via $\psi$. Let $b = (b_i)_{i \in \mathrm{Fin}\, n}$ be a $\mathbb C$-basis of the regular differentials of $F/\mathbb C$ (those $\omega$ which at each place $v$ equal $f \cdot v.\mathrm{dCoord}$ for some $f$ in the valuation ring of $v$), let $P_0$ be a place, and let $S \in M_n(\mathbb C)$ satisfy $\mathrm{tr}_\varphi(\psi^* b_j) = \sum_k S_{kj} b_k$ for all $j$, where the differential correspondence is `Differential.pullbackAlong` $\psi$ followed by `Differential.traceAlong` $\varphi$. Write $\Lambda$ for `pathPeriodLattice` $b$, the $\mathbb Z$-submodule of $\mathbb C^n$ spanned by the vectors $(\int_\gamma b_i)_i$ of path integrals along loops $\gamma$ at arbitrary places. Then: (1) $u S \in \Lambda$ for every $u \in \Lambda$ (row-vector multiplication `Matrix.vecMul`); and (2) for every divisor $D$ of $F/\mathbb C$ of degree $0$, writing $\mathrm{AJ}$ for `abelJacobiDiv` $b\, P_0$, the additive extension to divisors of $v \mapsto$ the vector of integrals of the $b_i$ along a chosen path from $P_0$ to $v$, one has $\mathrm{AJ}(\psi_* \varphi^* D) - \mathrm{AJ}(D)\, S \in \Lambda$.
--
--   This is Hurwitz's determination of the analytic representation of an algebraic correspondence $(\varphi, \psi)$ on a compact Riemann surface: on divisor classes of degree zero the correspondence $\psi_* \varphi^*$ acts, through the Abel–Jacobi map, by the transpose of the matrix of $\mathrm{tr}_\varphi \psi^*$ on the differentials of the first kind, and the period lattice is stable under that transpose. It is used to show that a correspondence acting trivially on regular differentials acts trivially on $\mathrm{Pic}^0$, and to produce the integral matrix describing the induced action on the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice.lean

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

theorem AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
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
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ j : Fin n, Differential.correspondence φ ψ (b j : Ω[F⁄ℂ]) =
      ∑ k : Fin n, S k j • (b k : Ω[F⁄ℂ])) :
    (∀ u ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])),
        Matrix.vecMul u S ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) ∧
    ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Divisor.correspondence φ ψ hφ hψ D) -
          Matrix.vecMul (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D) S ∈
        pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by sorry
