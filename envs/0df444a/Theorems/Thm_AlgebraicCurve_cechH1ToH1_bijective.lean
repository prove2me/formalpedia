-- Prove2me | Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
-- name    : AlgebraicCurve.cechH1ToH1_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/cff42170-0aff-5eb6-83cd-d723aa3ac340
-- title:
--   Two-chart Čech H¹ computes the répartition H¹(D)
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`: every nonzero $f \in F$ admits a finitely supported divisor recording its orders $v.\mathrm{ord}\,f$ at all places and having degree $0$, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; here a place is a valuation subring of $F$, different from $F$ itself, containing the image of $K$ and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places, of degree $\sum_v D(v)\deg v$. Assume moreover that $L(0) = \{f : v.\mathrm{adicValuation}\,f \le 1 \text{ for all } v\}$ is finite-dimensional over $K$, and that `RiemannGenusReachedAt γ D₀` holds for some $\gamma \in \mathbb{Z}$ and divisor $D_0$, i.e. $L(D_0) = \{f : v.\mathrm{adicValuation}\,f \le \exp(D_0 v)\ \forall v\}$ is finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Let $S_0, S_1$ be sets of places with $S_0 \cup S_1$ the set of all places, each of $S_0$, $S_1$ omitting at least one place, and let $D$ be any divisor. Then the comparison map `cechH1ToH1 hcover D` — induced on $\mathrm{lSpaceOn}\,(S_0 \cap S_1)\,D$ modulo the range of the Čech differential $(-r_0) \sqcup r_1$ from $\mathrm{lSpaceOn}\,S_0\,D \times \mathrm{lSpaceOn}\,S_1\,D$, by extension off the chart $S_0$ followed by the quotient map onto $H^1(D)$, the quotient of répartitions by $\mathrm{repartitionsOf}\,D + \mathrm{principalRepartitions}$ — is bijective.
--
--   This is the function-field form of the statement that the Čech complex of a cover of a curve by two affine charts computes $H^1$ of $\mathcal{O}(D)$, identified with the répartition (adelic) group $\mathbb{A}/(\mathbb{A}(D)+F)$. It is used to transport finiteness and dimension statements between the two descriptions, in the Čech form of the Riemann–Roch theorem under the attained-genus hypothesis and in the proof that the Serre pairing and its flip are bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_cechH1ToH1_bijective.lean

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

theorem cechH1ToH1_bijective {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    Function.Bijective (cechH1ToH1 hcover D) := by sorry
