-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
-- name    : AlgebraicCurve.exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/abbf337e-8565-56a2-a10d-ea732e177dce
-- title:
--   Period normalisation of a third-kind differential
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, assumed finitely generated in the sense that some $x \in F$ is transcendental over $\mathbb{C}$ and $F$ is finite-dimensional over $\mathbb{C}(x)$; assume `IsCurveOver ℂ F` (principal divisors, residue fields of all places finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ free of rank one over $F$) and `HasCanonicalDivisor`, so that for each nonzero $\omega \in \Omega[F/\mathbb{C}]$ the function $v \mapsto v.\mathrm{ordDifferential}\,\omega$ is a divisor. Assume the space `Place ℂ F` of places carries a topology and $\mathbb{C}$-charts making it a compact, Hausdorff, connected real-analytic one-dimensional complex manifold, and assume `hF`: for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{evalAt}_{(\mathrm{extChartAt}\,v)^{-1}(z)}(f)$ is meromorphic at the chart centre of $v$ with `meromorphicOrderAt` equal to $v.\mathrm{ord}\,f$. Fix $n$, a $\mathbb{C}$-basis $b$ of `regularDifferentials ℂ F` (the differentials that at each $v$ are $f \cdot v.\mathrm{dCoord}$ with $f$ in the valuation ring of $v$) indexed by `Fin n`, a base place $P_0$, and a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on places) of degree $0$. Let $\eta \in \Omega[F/\mathbb{C}]$ satisfy $v.\mathrm{ordDifferential}\,\eta \geq -1$ at every $v$, i.e. at worst simple poles, together with the residue normalisation $\mathrm{evalAt}_v\bigl(v.\mathrm{dCoordFn} \cdot v.\mathrm{differentialCoeff}\,\eta\bigr) = D(v)$ for every $v$, where $v.\mathrm{differentialCoeff}\,\eta$ is the coefficient in $\eta = h \cdot v.\mathrm{dCoord}$ and $v.\mathrm{dCoordFn}$ is the element of valuation one at $v$ chosen with $v.\mathrm{dCoord}$. Finally assume that $\mathrm{abelJacobiDiv}$ of $D$ for the family $(b_i)$ and base point $P_0$ — the additive extension of $v \mapsto (\int_{\gamma_v} b_i)_i$ along a chosen path from $P_0$ to $v$ — lies in `pathPeriodLattice`, the $\mathbb{Z}$-span of the vectors of loop integrals $(\int_\gamma b_i)_i$ over all loops $\gamma$. The conclusion: there exists a regular differential $\zeta$ such that for every place $P$ and every loop $\gamma : P \to P$ with $D(\gamma(t)) = 0$ for all $t$, the path integral of $\eta - \zeta$ along $\gamma$ equals $2\pi i m$ for some $m \in \mathbb{Z}$.
--
--   This is the transcendental step in the sufficiency half of Abel's theorem: a differential of the third kind with residues prescribed by a degree-zero divisor $D$ can, once the Abel–Jacobi image of $D$ is a period, be corrected by a holomorphic differential so that all its periods along loops missing the support of $D$ lie in $2\pi i \mathbb{Z}$. It is used by [`AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice), where exponentiating a primitive of $\eta - \zeta$ produces the function with divisor $D$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0)
    (η : Ω[F⁄ℂ]) (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff η) = (D v : ℂ))
    (hD : abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) :
    ∃ ζ ∈ regularDifferentials ℂ F, ∀ (P : Place ℂ F) (γ : Path P P),
      (∀ t, D (γ t) = 0) → ∃ m : ℤ, pathIntegral (η - ζ) γ = 2 * Real.pi * Complex.I * m := by sorry
