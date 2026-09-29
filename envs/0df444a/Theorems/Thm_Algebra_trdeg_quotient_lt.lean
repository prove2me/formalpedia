-- Prove2me | Theorems.Thm_Algebra_trdeg_quotient_lt
-- name    : Algebra.trdeg_quotient_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/73a23043-64e9-57a6-a757-0a7f61c5194c
-- title:
--   A nonzero proper ideal strictly drops transcendence degree
-- statement:
--   Let $K$ be a field and let $R$ be a commutative ring which is an integral domain and a $K$-algebra of finite type, i.e. generated as a $K$-algebra by finitely many elements. Let $I$ be an ideal of $R$ with $I \neq \bot$ (that is, $I$ contains a nonzero element) and $I \neq \top$ (that is, $I \neq R$, equivalently $R/I$ is nontrivial). Then the transcendence degree of the quotient algebra $R \mathbin{/} I$ over $K$ is strictly smaller than that of $R$ over $K$, $$\operatorname{trdeg}_K(R/I) < \operatorname{trdeg}_K(R),$$ the inequality being one of cardinals, where `Algebra.trdeg` is the supremum of the cardinalities $\#s$ of those subsets $s$ of the algebra that are algebraically independent over $K$. No separate finiteness hypothesis on the transcendence degrees is imposed: finite type over the field $K$ forces $\operatorname{trdeg}_K(R)$ to be finite, and the strict inequality is asserted in the cardinal order.
--
--   This is the algebraic form of the statement that a nonempty proper closed subscheme of an irreducible affine variety over a field has strictly smaller dimension. It is used in the project for finiteness and dimension arguments, being cited in the proof that a finite algebra map into a ring with the relevant fraction-field property is injective and in the computation of the Krull dimension of stalks under a locally quasi-finite endomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_trdeg_quotient_lt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Algebra.trdeg_quotient_lt {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] (I : Ideal R) (hI : I ≠ ⊥) (hI' : I ≠ ⊤) :
    Algebra.trdeg K (R ⧸ I) < Algebra.trdeg K R := by sorry
