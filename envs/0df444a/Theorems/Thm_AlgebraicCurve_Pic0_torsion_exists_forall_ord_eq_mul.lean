-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul
-- name    : AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d548d5e6-9820-5c60-87d0-5ae636fb5f33
-- title:
--   Witness function for an n-torsion divisor class
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $n$ be a natural number. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$; the degree homomorphism sends a divisor to the sum of its coefficients weighted by the degrees of the places, and $\mathrm{Div}^0$ is its kernel; $\mathrm{Pic}^0(F/K)$ is the quotient of $\mathrm{Div}^0$ by the subgroup of those degree-zero divisors $E$ that are principal, i.e. for which some $f \neq 0$ in $F$ satisfies $\mathrm{ord}_v(f) = E(v)$ at every place $v$, where $\mathrm{ord}_v$ is the negative of the logarithm of the associated adic valuation; and the $n$-torsion subgroup of $\mathrm{Pic}^0(F/K)$ is the $\mathbb{Z}$-torsion submodule for the element $(n : \mathbb{Z})$. The assertion: given an element $x$ of this $n$-torsion subgroup and a degree-zero divisor $D$ whose class in $\mathrm{Pic}^0(F/K)$ is $x$, there exists $f \in F$ with $f \neq 0$ such that $\mathrm{ord}_v(f) = n \cdot D(v)$ for every place $v$ of $F/K$.
--
--   This is the standard extraction, from an $n$-torsion divisor class, of a single nonzero function whose divisor is $n$ times a chosen representative — the input to the divisorial construction of the Weil pairing. It is used in [`AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`](thm.html#AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing), [`AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub`](thm.html#AlgebraicCurve.WeilDatum.pairing_eq_of_isPrincipal_sub) and [`AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F)) (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by sorry
