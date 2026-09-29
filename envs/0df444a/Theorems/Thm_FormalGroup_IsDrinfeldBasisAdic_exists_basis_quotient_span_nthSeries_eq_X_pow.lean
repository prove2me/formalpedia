-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow
-- name    : FormalGroup.IsDrinfeldBasisAdic.exists_basis_quotient_span_nthSeries_eq_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/1116195b-f625-5891-bb09-e68b559a6886
-- title:
--   Free rank q² basis of T[[X]]/([q]_F) at a Drinfeld basis
-- statement:
--   Let $T$ be a commutative ring, $I \subseteq T$ an ideal for which $T$ is $I$-adically complete (and separated), and let $F$ be a one-dimensional formal group law over $T$. Let $q$ be a natural number (no positivity is assumed) and let $x_0, x_1 \in I$. Write $F.nthSeries\,q \in T[[X]]$ for the $q$-division series of $F$, defined by recursion: $F.nthSeries\,0 = 0$ and $F.nthSeries\,(n+1)$ is the substitution of the pair $(F.nthSeries\,n, X)$ into the two-variable group law $F.toPowerSeries$, so that $F.nthSeries\,q = [q]_F(X)$. Assume `F.IsDrinfeldBasisAdic I q x₀ x₁`, that is, taking $I$ as the ideal governing the adic structure on $T$, there is a unit $u$ of $T[[X]]$ with $F.nthSeries\,q = u \cdot F.drinfeldDivisor\,q\,x_0\,x_1$, where `F.drinfeldDivisor q x₀ x₁` is the power series attached $I$-adically to the pair $(x_0,x_1)$ at level $q$. The conclusion asserts the existence of a $T$-basis $b$ of the quotient module $T[[X]] / (F.nthSeries\,q)$ indexed by $\mathrm{Fin}(q \cdot q)$ such that for every index $i$ the basis vector $b_i$ is the class of $X^{i}$. In particular this quotient is a free $T$-module of rank $q^2$ with basis the classes of $1, X, \dots, X^{q^2-1}$.
--
--   This is the rank count on the formal side of the comparison between formal and global Drinfeld bases: the coordinate ring of the kernel of multiplication by $q$ on the formal group $\mathrm{Spf}\,T[[X]]$ is finite free of rank $q^2$ once $[q]_F$ factors, up to a unit, through the divisor cut out by a Drinfeld basis. It feeds the deduction that a global Drinfeld basis of level $q$ arises from a formal one, used by [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.exists_basis_quotient_span_nthSeries_eq_X_pow
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (q : ℕ) (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I)
    (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    ∃ b : Module.Basis (Fin (q * q)) T (PowerSeries T ⧸ Ideal.span {F.nthSeries q}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {F.nthSeries q}) (PowerSeries.X ^ (i : ℕ)) := by sorry
