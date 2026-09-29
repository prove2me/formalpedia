-- Prove2me | Theorems.Thm_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top
-- name    : AlgebraicCurve.discreteTopology_pathPeriodLattice_and_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/da7ebca7-9d50-5b08-b7cb-a83f0547b4e6
-- title:
--   Path periods form a lattice in ℂⁿ
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, and assume $F$ is a function field in one variable over $\mathbb{C}$ in the sense that there is a transcendental element $x \in F$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x)$. Assume `IsCurveOver ℂ F`, i.e. every nonzero $f \in F$ has an associated divisor of degree $0$ whose value at each place $v$ is $\operatorname{ord}_v(f)$, each residue field of a place is finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$; assume also `HasCanonicalDivisor`, i.e. every nonzero differential $\omega$ has a divisor whose value at $v$ is $v.\mathrm{ordDifferential}\,\omega$. Suppose the space of places $\mathrm{Place}\,\mathbb{C}\,F$ carries a topology together with a $\mathbb{C}$-charted structure making it an analytic manifold modelled on $\mathbb{C}$, and that it is compact, Hausdorff and connected. Assume further the compatibility hypothesis `hF`: for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{Place.evalAt}\ (\text{chart}^{-1} z)\ f$ is meromorphic at the chart image of $v$, with meromorphic order there equal to $\operatorname{ord}_v(f)$. Finally let $b$ be a $\mathbb{C}$-basis of the space `regularDifferentials ℂ F` of differentials that at each place $v$ are of the form $f \cdot v.\mathrm{dCoord}$ with $f$ in the valuation subring of $v$, indexed by $\mathrm{Fin}\,n$. Then the subgroup `pathPeriodLattice` of $\mathbb{C}^n$ — the $\mathbb{Z}$-span of all vectors $\left(\int_\gamma b_i\right)_{i}$ obtained from loops $\gamma$ at a place $P$ — carries the discrete topology, and its $\mathbb{R}$-span is all of $\mathbb{C}^n$.
--
--   This is the classical statement that the periods of a basis of holomorphic differentials on a compact Riemann surface generate a full lattice in $\mathbb{C}^g$, the lattice underlying the Jacobian. It is used to realise $\mathrm{Pic}^0$ of the curve as a quotient of $\mathbb{C}^n$ by this lattice and, through that, in the comparison of Tate modules with integral matrices attached to correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.lean

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

theorem AlgebraicCurve.discreteTopology_pathPeriodLattice_and_span_eq_top
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
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    DiscreteTopology ↥(pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) ∧
      Submodule.span ℝ (pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) : Set (Fin n → ℂ)) = ⊤ := by sorry
