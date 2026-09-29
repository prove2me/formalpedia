-- Prove2me | Theorems.Thm_FormalGroup_eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul
-- name    : FormalGroup.eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/0aff9044-71ce-5fea-988b-03f07e386558
-- title:
--   Product-form generator of ker[q] is a root of the distinguished factor
-- statement:
--   Let $T$ be a Noetherian local commutative ring with maximal ideal $\mathfrak m$, complete (and separated) for the $\mathfrak m$-adic topology, let $F$ be a one-dimensional formal group law over $T$, and let $q$ be a prime. Write $F.nthSeries$ for the family of one-variable series defined by $F.nthSeries\,0 = 0$ and $F.nthSeries\,(n+1) = F(F.nthSeries\,n, X)$, so that $F.nthSeries\,q$ is the multiplication-by-$q$ series $[q]_F$, and for $a \in \mathbb N$ and $x \in T$ write $F.evalNSMul\,a\,x$ for the element of $T$ given by $F.evalNSMul\,0\,x = 0$ and $F.evalNSMul\,(a+1)\,x = F(F.evalNSMul\,a\,x, x)$, the two-variable series being evaluated $\mathfrak m$-adically. Assume: $g \in T[X]$ is monic with $\deg g = q-1$ and $g$'s coefficients in degrees $i < q-1$ all lie in $\mathfrak m$; $v \in T[[X]]$ is a unit; $[q]_F = X \cdot g \cdot v$ as power series; $x \in \mathfrak m$; and there exists a unit $u \in T[[X]]$ with $[q]_F = u \cdot \prod_{a=0}^{q-1}\bigl(X - F.evalNSMul\,a\,x\bigr)$. Then $g(x) = 0$.
--
--   This is the necessity half of the characterisation of Igusa-type generators: if the kernel of multiplication by $q$ on $F$ is cut out, in the product form of a full set of sections, by the successive $F$-multiples of a point $x$ of the maximal ideal, then $x$ is a root of the distinguished factor $g$ of $[q]_F$. It is used in the criterion [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod) identifying Drinfeld bases in terms of vanishing of the distinguished factor at the origin parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul.lean

import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul
    (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T)
    (hgen : ∃ u : PowerSeries T, IsUnit u ∧
        F.nthSeries q = u * ∏ a ∈ Finset.range q,
          (PowerSeries.X - PowerSeries.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a x))) :
    g.eval x = 0 := by sorry
