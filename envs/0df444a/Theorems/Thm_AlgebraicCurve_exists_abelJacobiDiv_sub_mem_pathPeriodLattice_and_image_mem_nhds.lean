-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
-- name    : AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/8c54aeaf-3365-5219-ae46-774d034ad88b
-- title:
--   Local Jacobi inversion for the lifted Abel–Jacobi map
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure such that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place $v$ is $\operatorname{ord}_v f$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. The set $\mathrm{Place}(\mathbb{C},F)$ of places (valuation subrings of $F$ containing $\mathbb{C}$, proper and principal) is assumed to carry a topology and a charted space structure over $\mathbb{C}$ making it a connected Hausdorff analytic ($\omega$) manifold, and the hypothesis `hF` requires that for every $f \neq 0$ and every place $v$ the function $z \mapsto \mathrm{evalAt}_{(\mathrm{extChartAt}\,v)^{-1}(z)}(f)$ is meromorphic at $\mathrm{extChartAt}\,v\,(v)$ with meromorphic order equal to $\operatorname{ord}_v f$, where $\mathrm{evalAt}_w(f)$ is the value in $\mathbb{C}$ obtained from the residue of $f$ when $f$ lies in the valuation subring of $w$ and $0$ otherwise. Given $n \in \mathbb{N}$, differentials $b_0,\dots,b_{n-1} \in \Omega[F/\mathbb{C}]$ each regular (for every place $w$, $b_i = f \cdot w.\mathrm{dCoord}$ for some $f$ in the valuation subring of $w$, with $w.\mathrm{dCoord} = D_{\mathbb{C}}$ of a uniformiser of $w$), places $v_0,\dots,v_{n-1}$ for which the matrix with $(i,j)$ entry $\mathrm{evalAt}_{v_j}$ of the $\mathrm{dCoord}$-coefficient of $b_i$ at $v_j$ has invertible determinant, and a base place $P_0$, there exists a map $\Phi$ from $n$-tuples of places to $\mathbb{C}^n$ such that $\Phi(v) = 0$; the image under $\Phi$ of every neighbourhood of $v$ is a neighbourhood of $0$ in $\mathbb{C}^n$; and for all $n$-tuples $P$ in a neighbourhood of $v$, the difference between the Abel–Jacobi vector (path integrals of the $b_i$ from $P_0$, extended additively to divisors) of the divisor $\sum_j P_j - \sum_j v_j$ and $\Phi(P)$ lies in the period lattice, the $\mathbb{Z}$-span of the vectors of path integrals of the $b_i$ along loops.
--
--   This is the local form of the Jacobi inversion theorem: near a tuple of places in general position for the chosen regular differentials, the Abel–Jacobi map into $\mathbb{C}^n$ modulo periods lifts to a map $\Phi$ into $\mathbb{C}^n$ that is open at the base tuple. It is used in the construction of a finite generating set for the period lattice, in [`AlgebraicCurve.exists_finset_card_le_span_eq_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_finset_card_le_span_eq_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds.lean

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
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
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
    (v : Fin n → Place ℂ F)
    (hv : IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
        (v j).evalAt ((v j).differentialCoeff (b i)))))
    (P₀ : Place ℂ F) :
    ∃ Φ : (Fin n → Place ℂ F) → (Fin n → ℂ), Φ v = 0 ∧
      (∀ U ∈ 𝓝 v, Φ '' U ∈ 𝓝 (0 : Fin n → ℂ)) ∧
      ∀ᶠ P in 𝓝 v,
        abelJacobiDiv b P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) - Φ P ∈
          pathPeriodLattice b := by sorry
