-- Prove2me | Theorems.Thm_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
-- name    : FormalGroup.coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a2145ac1-ba88-58fe-bae7-a86abcafe546
-- title:
--   Star-isomorphic lifts share the q-th coefficient of [q]
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $F_0$ a one-dimensional formal group law over $k$ satisfying `IsDrinfeldBasisAdic ⊥ q 0 0`: with respect to the zero ideal of $k$ there is a unit power series $u$ with $F_0$'s $q$-series, `F₀.nthSeries q` (the $n$-fold iterate defined by $[n+1] = F_0([n](X),X)$), equal to $u$ times `F₀.drinfeldDivisor q 0 0`; by the cited equivalence for the $\bot$-adic case this says $[q]_{F_0} = u\,X^{q^2}$. Let $T$ be a local commutative ring whose maximal ideal satisfies $\mathfrak m^2 = 0$, and let $\mathrm{res}_T : T \to k$ be a ring homomorphism with kernel exactly $\mathfrak m$. Let $G$ and $G'$ be formal group laws over $T$ which are both base changes of $F_0$ along $\mathrm{res}_T$, i.e. the power series of $G$ and of $G'$ each become the coefficientwise image of that of $F_0$ under $\mathrm{res}_T$. Let $\psi$ be a `LawIso` from $G$ to $G'$: a power series with zero constant term and unit linear coefficient satisfying $\psi(G(X,Y)) = G'(\psi(X),\psi(Y))$. Assume further that $\mathrm{res}_T$ sends the $m$-th coefficient of $\psi$ to $1$ for $m = 1$ and to $0$ otherwise, i.e. $\psi$ reduces to $X$ modulo $\mathfrak m$. Then the $q$-th coefficients of the $q$-series of $G$ and of $G'$ coincide.
--
--   This is the easy half of the Lubin–Tate description of the tangent space to the deformation functor of a height-two formal group law: star-isomorphic first-order lifts have the same $q$-th coefficient of their multiplication-by-$q$ series, so that this coefficient is an invariant of the star-isomorphism class. It feeds into the construction of a square-zero universal lift, [`FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries`](thm.html#FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot.lean

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

theorem FormalGroup.coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hker : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) (hG : G.IsBaseChange resT F₀) (hG' : G'.IsBaseChange resT F₀)
    (ψ : FormalGroup.LawIso G G') (hψ : ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0) :
    PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q) := by sorry
