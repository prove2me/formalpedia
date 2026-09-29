-- Prove2me | Theorems.Thm_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
-- name    : FormalGroup.exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/dc59a25c-e6a3-56d3-98e3-5775cfdc588b
-- title:
--   Isomorphic formal groups: Hasse coefficients agree up to a unit mod q
-- statement:
--   Let $R$ be a commutative ring and let $q$ be a natural number assumed prime (via a `Fact` instance). Let $F$ and $F'$ be one-dimensional formal group laws over $R$, each satisfying `FormalGroup.IsComm`, and let $\psi$ be a [`FormalGroup.LawIso`](def/FormalGroup_PointTransport.html#L24) from $F'$ to $F$: a power series $\psi$ over $R$ with zero constant term whose linear coefficient $\mathrm{coeff}_1\,\psi$ is a unit of $R$, and which intertwines the two laws in the sense that $\psi(F'(X_0,X_1)) = F(\psi(X_0),\psi(X_1))$. For a law $G$, the iterated multiplication series $G.\mathrm{nthSeries}$ is defined recursively by $[0]_G = 0$ and $[n+1]_G(Z) = G([n]_G(Z), Z)$. The conclusion is the existence of a unit $w \in R$ such that $$\mathrm{coeff}_q\big([q]_F\big) - w\,\mathrm{coeff}_q\big([q]_{F'}\big) \in (q) = \mathrm{Ideal.span}\,\{(q : R)\},$$ i.e. the $Z^q$-coefficients of the $q$-fold multiplication series of the two isomorphic laws differ by a unit factor modulo $q$. No normalisation of $w$ is asserted.
--
--   The coefficient $\mathrm{coeff}_q([q]_F)$ is the Hasse coefficient of the formal group law, and the statement says that it is an isomorphism invariant of the law modulo $q$ up to a unit scaling (classically $w = \psi'(0)^{1-q}$). It feeds the analysis of the Hasse invariant on moduli of elliptic curves, being cited by the two results on [`ModularCurve.LevelModuliPackageAbs`](def/ModularCurve_LevelModuliPackageAbs.html#L10) that compare such a coefficient with a value of the $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open FormalGroup

theorem FormalGroup.exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
    {R : Type u} [CommRing R] (q : ℕ) [Fact q.Prime]
    (F F' : FormalGroup R) [F.IsComm] [F'.IsComm] (ψ : FormalGroup.LawIso F' F) :
    ∃ w : R, IsUnit w ∧
      PowerSeries.coeff q (F.nthSeries q) - w * PowerSeries.coeff q (F'.nthSeries q) ∈ Ideal.span {(q : R)} := by sorry
