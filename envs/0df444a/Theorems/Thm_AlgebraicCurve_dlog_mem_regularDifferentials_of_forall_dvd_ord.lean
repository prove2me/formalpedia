-- Prove2me | Theorems.Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
-- name    : AlgebraicCurve.dlog_mem_regularDifferentials_of_forall_dvd_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/0433e650-5ef4-59d2-9614-99da7e00c84f
-- title:
--   Logarithmic differentials with p-divisible orders are regular
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect and $F$ essentially of finite type over $K$. Assume [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero element of $F$ has a degree-zero divisor whose value at each place is the order of that element, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, and $\operatorname{ord}_v$ is minus the logarithm of the associated adic valuation. Assume further that for every place $w$ the differential $d\pi_w$ of a uniformiser spans $\Omega_{F/K}$ over $F$. Let $p$ be a prime with $F$ of characteristic $p$, and let $f \in F$ be nonzero with $p \mid \operatorname{ord}_v(f)$ in $\mathbb{Z}$ for every place $v$. Then $f^{-1}\,d f$ lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26), that is, for every place $v$ there is an element $g$ of the valuation subring of $v$ with $f^{-1}\,df = g\,d\pi_v$.
--
--   This is the statement that a logarithmic differential $df/f$ is everywhere regular as soon as all its local orders are divisible by the characteristic, the local input to the embedding of $p$-torsion classes into the space of regular differentials. It is used in the proof that the $p$-torsion of $\operatorname{Pic}^0$ is finite in characteristic $p$, and in the construction of the maps from torsion to regular differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.dlog_mem_regularDifferentials_of_forall_dvd_ord
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {f : F} (hf : f ≠ 0) (h : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord f) :
    f⁻¹ • KaehlerDifferential.D K F f ∈ AlgebraicCurve.regularDifferentials K F := by sorry
