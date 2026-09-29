-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
-- name    : AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/b4bcfe3e-5c68-5a34-b36c-ebcd86aa4120
-- title:
--   Chart reading of h dg as Rᵥh·(Rᵥg)'
-- statement:
--   Let $F$ be a field equipped with a $\mathbb C$-algebra structure, assume $F$ contains an element $x$ transcendental over $\mathbb C$ with $F$ finite-dimensional over the intermediate field $\mathbb C(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place is $\mathrm{ord}_v f = -\log$ of the adic valuation of $f$, every place has residue field finite over $\mathbb C$, and $\Omega[F\!\mid\!\mathbb C]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing $\mathbb C$, proper, and a principal ideal ring. Let the set of places carry a Hausdorff topology and a charted space structure with model $\mathbb C$, and assume the compatibility hypothesis $hF$: for every $f \neq 0$ and every place $v$, the chart reading $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ (the image of $f$ in the residue field at $\varphi_v^{-1}(z)$ pulled back to $\mathbb C$, and $0$ where $f$ is not integral there) is meromorphic at $\varphi_v(v)$ with `meromorphicOrderAt` equal to $\mathrm{ord}_v f$, where $\varphi_v$ is the extended chart at $v$. Fix a place $v$, an element $g$ of its valuation subring, and an arbitrary $h \in F$. Then, writing $R_v f$ for the chart reading of $f$ and $\mathrm{readDifferential}_v(\omega) = R_v(c)\cdot (R_v\pi_v)'$ for $\omega = c\,d\pi_v$ with $\pi_v$ the chosen element of $\mathrm{ord}_v = 1$ whose differential generates: first, for all $z \neq \varphi_v(v)$ in a punctured neighbourhood of $\varphi_v(v)$, $\mathrm{readDifferential}_v(h \cdot d g)(z) = R_vh(z)\cdot (R_vg)'(z)$; and second, if $h$ also lies in the valuation subring of $v$, the same identity holds on a full neighbourhood of $\varphi_v(v)$.
--
--   This is the derivative dictionary between the algebraic Kähler differential $dg = (dg/d\pi_v)\,d\pi_v$ in $\Omega[F\!\mid\!\mathbb C]$ and complex differentiation in a chart; with $h = 1$ it is the chain rule $(R_vg)' = R_v(dg/d\pi_v)\cdot(R_v\pi_v)'$. It underlies the local computations with complex line integrals on the curve, and is used in the Abel–Jacobi estimates such as [`AlgebraicCurve.coeffIn_local_calculus`](thm.html#AlgebraicCurve.coeffIn_local_calculus) and [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) {g : F} (hg : g ∈ v.toValuationSubring) (h : F) :
    (∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential (h • KaehlerDifferential.D ℂ F g) z =
          v.chartRead h z * deriv (v.chartRead g) z) ∧
    (h ∈ v.toValuationSubring → ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential (h • KaehlerDifferential.D ℂ F g) z =
          v.chartRead h z * deriv (v.chartRead g) z) := by sorry
