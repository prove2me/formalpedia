-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
-- name    : AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/09e844d3-6efb-5c01-9dff-b57653fbd83b
-- title:
--   Change of uniformiser: dπ' = u dπ with u a v-unit
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect, $F$ essentially of finite type over $K$, and suppose $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $\mathrm{ord}_v f$, every place has residue field finite-dimensional over $K$, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Here a place $v$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring, and $\mathrm{ord}_v$ is minus the logarithm of the associated adic valuation, so that $\mathrm{ord}_v$ is the normalised integer-valued order function at $v$. Let $\pi, \pi' \in F$ both satisfy $\mathrm{ord}_v \pi = \mathrm{ord}_v \pi' = 1$, i.e. both are uniformisers at $v$. The assertion is that there exists $u \in F$ with $\mathrm{ord}_v u = 0$, a unit at $v$, such that in $\Omega_{F/K}$ one has $D_{K,F}(\pi') = u \cdot D_{K,F}(\pi)$, where $D_{K,F}$ denotes the universal derivation of $F$ over $K$.
--
--   This is the local comparison of differentials at a place: the image of a uniformiser under the universal derivation is determined up to a unit at that place, so the order at $v$ of a differential, measured against $d\pi$, is independent of the choice of uniformiser. It is used in the treatment of regular and polar differentials under constant field extension, and in the analysis of regular differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by sorry
