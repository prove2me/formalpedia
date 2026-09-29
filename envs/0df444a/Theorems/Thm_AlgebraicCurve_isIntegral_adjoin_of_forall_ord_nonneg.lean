-- Prove2me | Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
-- name    : AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/926846d9-743f-5935-bbb7-e64fb2222eed
-- title:
--   No poles where t is regular implies integrality over K[t]
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ of characteristic zero, and let $t \in F$ be transcendental over $K$, with $F$ finite-dimensional over the intermediate field $K(t) =$ `IntermediateField.adjoin K {t}`, and assume $F/K$ has principal divisors, i.e. every nonzero $f \in F$ admits a finitely supported function $D$ on the places of $F/K$ with $D(v) = \operatorname{ord}_v f$ for all $v$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring, and $\operatorname{ord}_v f$ is the negative of the logarithm of the value of $f$ under the adic valuation attached to the height-one prime of $v$. Let $z \in F$ be such that $\operatorname{ord}_v z \ge 0$ for every place $v$ with $\operatorname{ord}_v t \ge 0$. Then $z$ is integral over the $K$-subalgebra $K[t] =$ `Algebra.adjoin K {t}` of $F$.
--
--   This is the classical description of the integral closure of $K[t]$ in a one-variable function field $F/K$ as the intersection of the valuation rings of the places at which $t$ has no pole (Stichtenoth III.2.6). It is used repeatedly in the construction of integral models of modular curves, e.g. in the verification that $q$-expansion coefficients lie in the relevant chart algebras and in the analysis of maximal ideals and trace relations for level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (t : F) (ht : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] [AlgebraicCurve.HasPrincipalDivisors K F] (z : F) (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) : IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by sorry
