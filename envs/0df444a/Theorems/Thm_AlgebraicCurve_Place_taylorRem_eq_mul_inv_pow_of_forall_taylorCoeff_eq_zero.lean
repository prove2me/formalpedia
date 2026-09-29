-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
-- name    : AlgebraicCurve.Place.taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ca4ef208-7320-5895-b54a-0e51d01160c5
-- title:
--   Taylor remainder when the lower coefficients vanish
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing $\operatorname{algebraMap}(K)$, different from $F$ itself, and whose underlying ring is a principal ideal ring. Fix $t, f \in F$ and $e \in \mathbb{N}$. Recall the remainders $\rho_r = \mathtt{taylorRem}\,v\,t\,f\,r$ defined by $\rho_0 = f$ and $\rho_{r+1} = (\rho_r - \operatorname{algebraMap}_{K,F}(v.\mathtt{evalAt}\,\rho_r))\cdot t^{-1}$, and the coefficients $a_r = \mathtt{taylorCoeff}\,v\,t\,r\,f = v.\mathtt{evalAt}\,\rho_r \in K$, where $v.\mathtt{evalAt}\,g$ is the residue of $g$ in the residue field of the valuation subring, transported to $K$ via $v.\mathtt{residueInv}$, when $g$ lies in the valuation subring, and $0$ otherwise. The hypothesis is that $a_q = 0$ for every $q < e$. The conclusion is the identity $\rho_e = f \cdot (t^{-1})^{e}$ in $F$. No hypothesis is imposed on $t$ (in particular $t = 0$ is allowed, $t^{-1}$ then being $0$), on $f$, or on the relation between $t$ and $v$.
--
--   This unwinds the defining recursion for the Taylor remainders of $f$ at $v$ along $t$: while the successive coefficients vanish, nothing is subtracted and each step only multiplies by $t^{-1}$. It is the bridge between vanishing of Taylor coefficients and the functions $f\,t^{-e}$ whose values give the regularised values of $f$, and is used in the comparison of coefficient vanishing with the order $\operatorname{ord}_v f$ ([`AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord`](thm.html#AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord), [`AlgebraicCurve.Place.taylorCoeff_ord_ne_zero`](thm.html#AlgebraicCurve.Place.taylorCoeff_ord_ne_zero)) and in [`AlgebraicCurve.Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero`](thm.html#AlgebraicCurve.Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorRem v t f e = f * t⁻¹ ^ e := by sorry
