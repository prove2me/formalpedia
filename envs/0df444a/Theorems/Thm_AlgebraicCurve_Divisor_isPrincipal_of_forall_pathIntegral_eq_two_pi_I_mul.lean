-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul
-- name    : AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/88b6bd22-413d-585e-9687-598c01f092ef
-- title:
--   Integral residues and periods in 2π iℤ give a principal divisor
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure such that some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x)$, and assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a divisor of degree $0$, every place has residue field finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing $\mathbb{C}$, different from $F$, whose valuation ring is a principal ideal ring, and $v.\mathrm{ord}$ is the associated normalised integer valuation. Suppose the set of places carries a topology and $\mathbb{C}$-charts making it a compact, connected, Hausdorff analytic manifold, and that for each nonzero $f \in F$ and each place $v$ the function $z \mapsto \mathrm{evalAt}\,f$ at the place $(\mathrm{extChartAt}\,v)^{-1}(z)$ is meromorphic at the centre $\mathrm{extChartAt}\,v\,(v)$ with `meromorphicOrderAt` equal to $v.\mathrm{ord}\,f$. Let $D$ be a finitely supported integer-valued function on places and $\theta \in \Omega[F/\mathbb{C}]$ with $-1 \le v.\mathrm{ordDifferential}\,\theta$ for all $v$, where $v.\mathrm{ordDifferential}\,\theta$ is the order of the coefficient $h_v$ in $\theta = h_v \cdot \mathrm{d}\pi_v$; assume the residue condition that $\mathrm{evalAt}_v(\pi_v h_v) = D(v)$ for every $v$, where $\pi_v$ is the chosen element `dCoordFn v`. Assume finally that for every place $P$ and every loop $\gamma$ at $P$ avoiding the support of $D$ (i.e. $D(\gamma(t)) = 0$ for all $t$) the path integral of $\theta$ along $\gamma$ lies in $2\pi i \mathbb{Z}$. Then $D$ is principal: there is $f \neq 0$ in $F$ with $D(v) = v.\mathrm{ord}\,f$ for all $v$.
--
--   This is the classical statement that a differential with at worst simple poles, integral residues and periods in $2\pi i\mathbb{Z}$ is a logarithmic differential $\mathrm{d}f/f$, so that its residue divisor is the divisor of a function. It is the analytic input used in the Abel–Jacobi criterion for principality of a degree-zero divisor on the curve of places of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul.lean

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

theorem AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul
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
    (D : Divisor ℂ F) (θ : Ω[F⁄ℂ]) (hθ : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ)
    (hres : ∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (γ : Path P P), (∀ t, D (γ t) = 0) →
      ∃ m : ℤ, pathIntegral θ γ = 2 * Real.pi * Complex.I * m) :
    Divisor.IsPrincipal D := by sorry
