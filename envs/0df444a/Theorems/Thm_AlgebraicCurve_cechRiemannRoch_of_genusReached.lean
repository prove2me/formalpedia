-- Prove2me | Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
-- name    : AlgebraicCurve.cechRiemannRoch_of_genusReached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/40949827-643b-5d64-a89c-8e56fd41e05d
-- title:
--   Čech Riemann–Roch on a two-chart cover of a curve
-- statement:
--   Let $K\subseteq F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F` (principal divisors, each residue field $v.\mathrm{ResidueField}$ finite over $K$, and $\Omega_{F/K}$ free of rank one over $F$), and assume the Riemann–Roch space $L(0)$ of the zero divisor is finite-dimensional over $K$. Let $\gamma\in\mathbb Z$ and let $D_0$ be a divisor (a finitely supported $\mathbb Z$-valued function on the places of $F/K$) with `RiemannGenusReachedAt γ D₀`, i.e. $L(D_0)$ is finite-dimensional, $\deg D_0-\ell(D_0)=\gamma-1$, and $\deg D-\ell(D)\le\gamma-1$ for every divisor $D$. Let $S_0,S_1$ be sets of places with $S_0\cup S_1$ the set of all places, each of $S_0,S_1$ omitting at least one place, and let $D$ be any divisor. Write $L_S(D)=\{f\in F:\ v(f)\le \exp(D v)\ \text{for all } v\in S\}$, and let $\check H^0=$ `cechH0 S₀ S₁ D` and $\check H^1=$ `cechH1 S₀ S₁ D` be the kernel and the cokernel of the difference map $L_{S_0}(D)\times L_{S_1}(D)\to L_{S_0\cap S_1}(D)$. Then: $\check H^0$ is finite-dimensional over $K$; $\check H^1$ is a finite $K$-module; $\dim_K\check H^0=\ell(D)=\dim_K L(D)$; $\dim_K\check H^1=i(D)$, the $K$-dimension of the quotient of the adele space by the sum of the $D$-bounded adeles and the diagonal image of $F$; $\dim_K\check H^0-\dim_K\check H^1=\deg D+1-\gamma$; and if $D_0\le D$ then $\check H^1$ is a subsingleton.
--
--   This is the Riemann–Roch theorem for the line bundle $\mathcal O(D)$ on the curve with function field $F$, in the form of the cohomology of the two-chart Čech complex attached to a cover of the set of places by $S_0$ and $S_1$: $h^0-h^1=\deg D+1-\gamma$ with both terms finite, together with vanishing of $h^1$ above a divisor realising the Riemann bound. It is the form used downstream for finiteness and dimension counts for the structure sheaf and for sections of divisors on smooth proper curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem cechRiemannRoch_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by sorry
