-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
-- name    : AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/4672620d-b49e-59ef-8d58-f2051d0c53ca
-- title:
--   Gauss-norm integrality at a residually transcendental point
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field which is an $L$-algebra, and $\bar F$ a field which is an algebra over the residue field $k = \mathrm{ResidueField}\,A$ of the local ring $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$, that is: a valuation subring $\mathcal{O} = R.\mathrm{integers}$ of $F$ together with a ring homomorphism $R.\mathrm{residue} \colon \mathcal{O} \to \bar F$ such that an element of $L$ lies in $A$ precisely when its image in $F$ lies in $\mathcal{O}$, $R.\mathrm{residue}$ is surjective with kernel the maximal ideal of $\mathcal{O}$, $R.\mathrm{residue}$ agrees on the image of $A$ with the structure map $k \to \bar F$ composed with the residue map of $A$, and every nonzero $f \in F$ admits a scalar $c \in L$ with $c \cdot f \in \mathcal{O}$ and $R.\mathrm{residue}(c \cdot f) \neq 0$. Let $x \in \mathcal{O}$ be such that $R.\mathrm{residue}(x)$ is transcendental over $k$, and let $c \in L[X]$ be a polynomial whose value $c(x)$ at the image of $x$ in $F$ lies in $\mathcal{O}$. Then for every $i \in \mathbb{N}$ the coefficient $c_i$ of $c$ lies in $A$.
--
--   This is the integrality half of the Gauss-norm description of a residually transcendental prolongation: the polynomial expressions in $x$ over $L$ that are integral at $\mathcal{O}$ are exactly those with coefficients in $A$. It is used in the construction of Gauss bases and of monic polynomials of controlled degree over such a prolongation, and thence in the identification of $\mathcal{O}$ by a finrank condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (c : Polynomial L) (hc : Polynomial.aeval (x : F) c ∈ R.integers) (i : ℕ) :
    c.coeff i ∈ A := by sorry
