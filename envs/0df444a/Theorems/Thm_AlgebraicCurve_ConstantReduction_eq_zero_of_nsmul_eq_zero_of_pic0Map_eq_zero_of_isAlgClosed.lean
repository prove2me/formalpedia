-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
-- name    : AlgebraicCurve.ConstantReduction.eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/952f208e-d27f-5add-beaf-3c4ccd955ddd
-- title:
--   Reduction is injective on m-torsion of Pic⁰ under good constant reduction
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $k=\mathrm{ResidueField}(A)$, and $F$ a field equipped with an $L$-algebra structure which is an algebraic function field of one variable over $L$, in the sense that there exists $x\in F$ transcendental over $L$ with $F$ finite-dimensional over the intermediate field $L(x)$. Let $\bar F$ be a field equipped with a $k$-algebra structure, and let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$: a valuation subring $\mathcal O\subseteq F$, a surjective ring homomorphism $\mathrm{res}\colon\mathcal O\to\bar F$ whose kernel is the maximal ideal of $\mathcal O$, and a map $P\mapsto\bar P$ from places of $F/L$ to places of $\bar F/k$ (places being valuation subrings containing the constants, proper, and principal ideal rings), subject to: for $x\in L$ one has $x\in A$ iff its image lies in $\mathcal O$; $\mathrm{res}$ agrees on $A$ with $A\to k\to\bar F$; every nonzero $f\in F$ satisfies $c f\in\mathcal O$ with $\mathrm{res}(cf)\neq0$ for some $c\in L$; $\deg\bar P=\deg P$; and for $f\in\mathcal O$ with $\mathrm{res}(f)\neq0$ the pushforward of $\mathrm{div}(f)$ along $P\mapsto\bar P$ is $\mathrm{div}(\mathrm{res}(f))$. Assume $R$ is good, i.e. $\mathrm{genusFF}(k,\bar F)=\mathrm{genusFF}(L,F)$, both genera being defined as the $\,$-dimension of $H^1(0)$. Let $m\in\mathbb N$ have nonzero image in $k$, and let $z$ lie in $\mathrm{Pic}^0(F/L)$, the group of degree-zero divisors modulo principal divisors, with $m\cdot z=0$ and with $z$ mapping to $0$ under the homomorphism $\mathrm{Pic}^0(F/L)\to\mathrm{Pic}^0(\bar F/k)$ induced by pushforward of divisors. Then $z=0$.
--
--   This is the injectivity of reduction on prime-to-residue-characteristic torsion of the degree-zero divisor class group under a good constant reduction, in the style of Deuring's reduction theory of function fields and of the classical lemma on reduction of divisor classes of finite order prime to the residue characteristic. It is the source of the finiteness and counting statements for torsion in $\mathrm{Pic}^0$ over such fields, and of the comparison of $m$-torsion between a function field and its good constant reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.eq_zero_of_nsmul_eq_zero_of_pic0Map_eq_zero_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧ FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (m : ℕ) (hm : (m : IsLocalRing.ResidueField A) ≠ 0)
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    z = 0 := by sorry
