-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
-- name    : FormalGroup.IsDrinfeldBasisAdic.exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/edc7af2a-ba6d-5995-934e-5790671634b9
-- title:
--   Transporting a Drinfeld basis along an isomorphism of formal group laws
-- statement:
--   Let $R$ be a commutative local ring which is complete and separated for the adic filtration of its maximal ideal $\mathfrak m$. Let $F'$ and $F$ be one-dimensional formal group laws over $R$ and let $\psi$ be a [`FormalGroup.LawIso`](def/FormalGroup_PointTransport.html#L24) from $F'$ to $F$, that is, a power series with vanishing constant term satisfying the compatibility $\psi(F'(X_0,X_1)) = F(\psi(X_0),\psi(X_1))$ and having invertible linear coefficient. Let $q$ be a natural number with $2 \le q$ and let $x_0, x_1 \in \mathfrak m$. Assume that $(x_0,x_1)$ is an $\mathfrak m$-adic Drinfeld basis of level $q$ for $F$, i.e. that, with $\mathfrak m$ taken as the distinguished ideal of $R$, there is a unit power series $u$ with $F.\mathrm{nthSeries}\,q = u \cdot F.\mathrm{drinfeldDivisor}\,q\,x_0\,x_1$, where `nthSeries` is defined by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}(n+1) = F(\mathrm{nthSeries}\,n, X)$, so that $\mathrm{nthSeries}\,q$ is the multiplication-by-$q$ series of the law. Assume further that $\mathfrak m = (x_0,x_1)$, and that the multiplication-by-$q$ series of $F'$ factors as $F'.\mathrm{nthSeries}\,q = P \cdot U$ with $P$ a polynomial over $R$ (viewed as a power series) and $U$ an invertible power series. Then there exist $y_0, y_1 \in \mathfrak m$ with $\mathfrak m = (y_0,y_1)$ and $P(y_0) = P(y_1) = 0$.
--
--   This is the transport of a Drinfeld basis of level $q$ from $F$ to $F'$ along the inverse of an isomorphism of formal group laws, combined with the observation that a basis point is a root of the polynomial part of the multiplication-by-$q$ series. It feeds the finiteness statement [`FormalGroup.IsDrinfeldBasisAdic.finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.finite_of_lawIso_isBaseChange_powerSeries_of_maximalIdeal_eq_span_pair_of_isComm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.exists_maximalIdeal_eq_span_pair_and_eval_eq_zero_of_lawIso
    {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (F' F : FormalGroup R) (ψ : FormalGroup.LawIso F' F)
    (q : ℕ) (hq : 2 ≤ q) (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)
    (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (P : Polynomial R) (U : PowerSeries R) (hU : IsUnit U)
    (hP : F'.nthSeries q = (P : PowerSeries R) * U) :
    ∃ y₀ y₁ : R, y₀ ∈ maximalIdeal R ∧ y₁ ∈ maximalIdeal R ∧
      maximalIdeal R = Ideal.span {y₀, y₁} ∧ P.eval y₀ = 0 ∧ P.eval y₁ = 0 := by sorry
