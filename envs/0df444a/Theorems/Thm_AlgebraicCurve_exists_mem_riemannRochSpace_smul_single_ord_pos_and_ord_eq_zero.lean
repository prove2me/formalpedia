-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/07795137-ec6c-5e4b-aea0-54d3dc2643bc
-- title:
--   Functions in L((2g+1)c) separating two places
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field that is a $k$-algebra which is essentially of finite type over $k$ and is a curve over $k$ in the sense of the class `IsCurveOver`: every nonzero $f \in F$ has a principal divisor, namely a finitely supported $\mathbb{Z}$-valued function on places whose value at each place $v$ is $v.\mathrm{ord}\,f = -\log v.\mathrm{adicValuation}(f)$ and whose degree is $0$; each place has residue field finite over $k$; and $\Omega_{F/k}$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $k$, distinct from $F$ itself, whose valuation ring is a principal ideal ring. Let $c$, $s$, $s'$ be places with $s \neq c$, $s' \neq c$ and $s \neq s'$, and write $g =$ `genusFF k F`, the $k$-dimension of $H^1$ of the zero divisor. Then there exists $h \in F$ lying in the Riemann–Roch space of the divisor $(2g+1)\,\delta_c$ — that is, $v.\mathrm{adicValuation}(h) \le \exp(D v)$ for every place $v$, where $D = (2g+1)\,\delta_c$, so $h$ has poles only at $c$ and there of order at most $2g+1$ — such that $s.\mathrm{ord}\,h > 0$ and $s'.\mathrm{ord}\,h = 0$.
--
--   This is the point-separating half of the classical statement that a divisor of degree at least $2g+1$ on a curve over an algebraically closed field is very ample: a function with poles confined to $c$ that vanishes at $s$ and is a unit at $s'$. It is used in the construction of charts on components and of coverings, and in producing separating functions on modular curves that are regular at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (c s s' : Place k F) (hsc : s ≠ c) (hs'c : s' ≠ c) (hss' : s ≠ s') :
    ∃ g : F, g ∈ riemannRochSpace (((2 * genusFF k F + 1 : ℕ) : ℤ) • Finsupp.single c (1 : ℤ)) ∧
      0 < s.ord g ∧ s'.ord g = 0 := by sorry
