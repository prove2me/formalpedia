-- Prove2me | Theorems.Thm_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
-- name    : FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/e3b2649f-9bfb-5c62-bacf-ffc4077f7428
-- title:
--   Frobenius factorisation of a law homomorphism with zero linear term
-- statement:
--   Let $S$ be a commutative ring, let $q$ be a prime, and suppose $S$ has characteristic $q$. Let $F$ and $G$ be one-dimensional formal group laws over $S$ (elements of `FormalGroup S`), and let $\theta$ be a `LawHom` from $F$ to $G$: that is, a power series $\theta.\mathrm{series} \in S[[X]]$ with zero constant coefficient satisfying the homomorphism identity $\theta(F(X_0,X_1)) = G(\theta(X_0),\theta(X_1))$, formulated as the equality of the substitution of $F$'s two-variable power series into $\theta.\mathrm{series}$ with the substitution of the pair $\theta(X_0), \theta(X_1)$ into $G$'s two-variable power series. Assume the degree-one coefficient of $\theta.\mathrm{series}$ vanishes. Then there exists a `LawHom` $\theta_1$ from $F.\mathrm{map}\,(\mathrm{frobenius}\,S\,q)$, the formal group law obtained by applying the $q$-power Frobenius endomorphism of $S$ to the coefficients of $F$, to $G$, such that for every natural number $n$ the $n$-th coefficient of $\theta_1.\mathrm{series}$ equals the $(qn)$-th coefficient of $\theta.\mathrm{series}$. In particular $\theta$ factors as $\theta_1$ precomposed with $X \mapsto X^q$.
--
--   This is the standard factorisation of a homomorphism of formal group laws in characteristic $q$ with vanishing linear term through the Frobenius twist: if the linear term dies, all coefficients in degrees prime to $q$ die, and the homomorphism is a homomorphism from the Frobenius twist of its source, re-indexed by division by $q$. It is used in the analysis of the $n$-series and of isomorphisms of formal group laws over rings with square-zero maximal ideal, being cited by [`FormalGroup.nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow`](thm.html#FormalGroup.nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow), [`FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot`](thm.html#FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot) and [`FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
    {S : Type u} [CommRing S] (q : ℕ) [Fact q.Prime] [CharP S q]
    {F G : FormalGroup S} (θ : FormalGroup.LawHom F G) (h1 : PowerSeries.coeff 1 θ.series = 0) :
    ∃ θ₁ : FormalGroup.LawHom (F.map (frobenius S q)) G,
      ∀ n : ℕ, PowerSeries.coeff n θ₁.series = PowerSeries.coeff (q * n) θ.series := by sorry
