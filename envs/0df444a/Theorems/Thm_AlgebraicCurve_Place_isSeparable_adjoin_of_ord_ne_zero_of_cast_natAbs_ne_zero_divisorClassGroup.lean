-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup
-- name    : AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8a9e23bd-4365-5111-9c4f-18102b5e7004
-- title:
--   Separability of F/K(t) when ordᵥ t is tame
-- statement:
--   Let $K$ be a perfect field and $F$ a field which is a $K$-algebra. Let $x \in F$ be such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F(a)$ for every $a \in K$, different from all of $F$, and whose underlying ring is a principal ideal ring. For $f \in F$ write $\operatorname{ord}_v f = -\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$, so $\operatorname{ord}_v$ is the normalised integer valuation of $v$. Let $t \in F$ satisfy $\operatorname{ord}_v t \neq 0$ and suppose moreover that the natural number $|\operatorname{ord}_v t|$ has nonzero image in $K$ under the canonical ring map $\mathbb{N} \to K$ (a tameness condition: the order of $t$ at $v$ is prime to the characteristic of $K$). The conclusion is that $F$ is a separable algebra over the intermediate field $K(t) =$ `IntermediateField.adjoin K {t}`.
--
--   This is the standard criterion from the theory of algebraic function fields of one variable: an element whose order at some place is nonzero and prime to the characteristic generates a subfield over which the whole function field is separable. It is used in the construction of local models of the modular curves $X_H$ at $p$, where it feeds into [`ModularCurve.XHDRModelAtP.exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin`](thm.html#ModularCurve.XHDRModelAtP.exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval_chartAlgFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero_divisorClassGroup
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (htame : (((v.ord t).natAbs : ℕ) : K) ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by sorry
