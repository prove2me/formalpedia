-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex
-- name    : AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/a89dd7d0-4827-581e-bbcf-75fdf78d1224
-- title:
--   Abel–Jacobi: Pic⁰ of a complex curve as ℂ^g/L
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, and assume `hfg`: there is $x \in F$ transcendental over $\mathbb{C}$ such that $F$ is finite-dimensional over the intermediate field $\mathbb{C}(x)$ obtained by adjoining $x$. Assume the instances `IsCurveOver ℂ F` — every nonzero $f \in F$ admits a finitely supported divisor with value $\operatorname{ord}_v f$ at each place $v$ and of degree $0$, every residue field of a place is finite-dimensional over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$ — and `HasCanonicalDivisor`, which provides for each nonzero Kähler differential $\omega$ a finitely supported divisor whose value at $v$ is $v.\mathrm{ordDifferential}\,\omega$; write $g =$ `genus ℂ F`, which is $(\deg D + 2)/2$ for the divisor of some nonzero differential (and $0$ if none exists). Assume further that the set `Place ℂ F` of places carries a topology and a $\mathbb{C}$-charted space structure making it a compact, Hausdorff, connected analytic manifold with model $\mathbb{C}$, and `hF`: for every nonzero $f \in F$ and every place $v$, the function $z \mapsto$ `Place.evalAt` $f$ at the point $(\text{extChartAt } v)^{-1}(z)$ is meromorphic at $\text{extChartAt } v\,(v)$ with meromorphic order there equal to $\operatorname{ord}_v f = -\log$ of the adic valuation of $f$. Then there exists a $\mathbb{Z}$-submodule $L$ of $\mathbb{C}^g$ (functions $\mathrm{Fin}\,g \to \mathbb{C}$) which is free and finite over $\mathbb{Z}$ with $\operatorname{rank}_{\mathbb{Z}} L = 2g$, together with an isomorphism of additive groups between `Pic0 ℂ F`, the quotient of the degree-zero divisors by the principal ones, and $\mathbb{C}^g / L$.
--
--   This is the Abel–Jacobi theorem, together with Abel's theorem in both directions, for a function field in one variable over $\mathbb{C}$ whose set of places is presented as a compact Riemann surface with analytic orders matching the valuations: the degree-zero divisor class group is the complex torus $\mathbb{C}^g$ modulo a lattice of rank $2g$. It feeds the statement [`AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex`](thm.html#AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex), where the Riemann-surface structure is no longer assumed as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex
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
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)) :
    ∃ (L : Submodule ℤ (Fin (genus ℂ F) → ℂ)),
      Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = 2 * genus ℂ F ∧
      Nonempty (Pic0 ℂ F ≃+ (Fin (genus ℂ F) → ℂ) ⧸ L) := by sorry
