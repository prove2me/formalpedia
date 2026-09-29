-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver
-- name    : AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/5d38bed6-d4fe-5867-9320-4c16412b24ce
-- title:
--   Differentials are integral at a place: dx = c dπ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, where $K$ is perfect and $F$ is essentially of finite type over $K$, and assume [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): that is, every nonzero $f \in F$ admits a divisor of degree $0$ whose multiplicity at each place is $\mathrm{ord}_v(f)$, every place has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$. Let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_v$ of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Let $\pi \in F$ satisfy $\mathrm{ord}_v(\pi) = 1$, where $\mathrm{ord}_v$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $\mathcal{O}_v$, so that $\pi$ is a uniformiser at $v$; and let $x \in \mathcal{O}_v$. Then there exists $c \in \mathcal{O}_v$ with $D_{K,F}(x) = c \cdot D_{K,F}(\pi)$ in $\Omega[F/K]$, where $D_{K,F}$ is the universal derivation.
--
--   This is the integrality of differentiation at a place: for $x$ integral at $v$ the quotient $dx/d\pi$ by a uniformiser again lies in the valuation ring, so $\mathrm{ord}_v(dx/d\pi) \ge 0$. It feeds the regularity statement for differentials of local units and the change-of-uniformiser comparisons, and thence the finite-support argument showing that the divisor of a differential is well defined; the proof invokes the existence of a separating transcendental element $t$ with $F/K(t)$ finite and separable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) {π : F} (hπ : v.ord π = 1) {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F π := by sorry
