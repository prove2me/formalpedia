-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
-- name    : AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/e69efec5-dae1-53f4-a9e5-92ed7d9b63bc
-- title:
--   Attained valuation in partial Riemann–Roch spaces L_S(D)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra such that $F/K$ is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has a divisor recording its orders $\operatorname{ord}_v f$ at all places and of degree $0$, each residue field $v.\mathrm{ResidueField}$ is finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, with associated $\mathbb{Z}^{m0}$-valued valuation `adicValuation`, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Assume moreover that $L(0) = \{f : v.\mathrm{adicValuation}\, f \le 1 \text{ for all } v\}$ is finite-dimensional over $K$, and that $\gamma \in \mathbb{Z}$ and a divisor $D_0$ satisfy `RiemannGenusReachedAt`: $L(D_0)$ is finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. Let $S$ be a set of places admitting a place $v_0 \notin S$, let $D$ be a divisor and let $v \in S$. Then there is $f \in F$ lying in `lSpaceOn S D`, that is $w.\mathrm{adicValuation}\, f \le \exp(D(w))$ for all $w \in S$, and with $v.\mathrm{adicValuation}\, f = \exp(D(v))$ exactly.
--
--   This is a refinement of strong approximation for function fields: inside the partial Riemann–Roch space $L_S(D)$ of elements bounded by $D$ at the places of $S$ only, the bound at any prescribed place of $S$ is actually attained (equivalently $\operatorname{ord}_v f = -D(v)$). It serves to show that $L_S(D)$ determines $D$ on $S$, and is used in the comparison of presentations of modules over curves in [`AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (S : Set (AlgebraicCurve.Place K F)) {v₀ : AlgebraicCurve.Place K F} (hv₀ : v₀ ∉ S)
    (D : AlgebraicCurve.Divisor K F) (v : AlgebraicCurve.Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ AlgebraicCurve.lSpaceOn S D ∧ v.adicValuation f = WithZero.exp (D v) := by sorry
