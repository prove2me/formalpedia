-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_nsmul_eq_zero_and_pic0Map_eq_of_nsmul_eq_zero
-- name    : AlgebraicCurve.ConstantReduction.exists_nsmul_eq_zero_and_pic0Map_eq_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/222f4400-e7cf-5835-9c04-516a920fa6c2
-- title:
--   Lifting m-torsion classes through a good constant reduction
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with residue field $k = \mathrm{ResidueField}(A)$; let $F$ be a field extension of $L$ admitting some $x \in F$ transcendental over $L$ with $F$ finite-dimensional over $L(x)$, and let $\bar F$ be a field extension of $k$. Let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$, that is: a valuation subring $\mathcal{O} \subseteq F$ (`R.integers`), a surjective ring homomorphism $\mathcal{O} \to \bar F$ (`R.residue`) whose kernel is the maximal ideal of $\mathcal{O}$ and which restricts on $A$ to the map $A \to k \to \bar F$, with $a \in A$ iff the image of $a$ in $F$ lies in $\mathcal{O}$, such that every nonzero $f \in F$ has $c \in L$ with $c \cdot f \in \mathcal{O}$ of nonzero residue, together with a map `R.placeMap` from places of $F/L$ to places of $\bar F/k$ preserving degrees and sending, for $f \in \mathcal{O}$ of nonzero residue, the divisor of $f$ (the divisor $D$ with $D(P) = \mathrm{ord}_P(f)$) to the divisor of its residue under pushforward of divisors. Assume $R$ is good, i.e. $\mathrm{genusFF}(k,\bar F) = \mathrm{genusFF}(L,F)$, both genera being defined as the $K$-dimension of $H^1$ of the zero divisor. Let $m$ be a natural number whose image in $k$ is nonzero, and let $y$ be a class in $\mathrm{Pic}^0(\bar F/k)$ — degree-zero divisors modulo principal divisors — with $m \cdot y = 0$. Then there is a class $z \in \mathrm{Pic}^0(F/L)$ with $m \cdot z = 0$ whose image under the reduction homomorphism `R.pic0Map`, induced by pushforward along `R.placeMap`, is $y$.
--
--   This is the surjectivity half of the classical statement that a good constant reduction induces an isomorphism on $m$-torsion of the Jacobian for $m$ invertible in the residue field (Deuring's theory of reduction of algebraic function fields modulo prime divisors of the constant field). Combined with the corresponding injectivity statement, it is used to compute the cardinality of the $\ell$-torsion of $\mathrm{Pic}^0$ as $\ell^{2g}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_exists_nsmul_eq_zero_and_pic0Map_eq_of_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.exists_nsmul_eq_zero_and_pic0Map_eq_of_nsmul_eq_zero
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧ FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (m : ℕ) (hm : (m : IsLocalRing.ResidueField A) ≠ 0)
    (y : Pic0 (IsLocalRing.ResidueField A) Fbar) (hy : m • y = 0) :
    ∃ z : Pic0 L F, m • z = 0 ∧ R.pic0Map z = y := by sorry
