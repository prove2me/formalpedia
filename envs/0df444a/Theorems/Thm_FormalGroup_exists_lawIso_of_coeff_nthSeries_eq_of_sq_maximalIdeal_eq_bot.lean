-- Prove2me | Theorems.Thm_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
-- name    : FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9a660fc1-83f2-5b2e-b933-153b94918e80
-- title:
--   Rigidity of square-zero lifts with equal q-series coefficient
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $F_0$ a commutative one-dimensional formal group law over $k$ satisfying the predicate `IsDrinfeldBasisAdic` for the ideal $\bot$ with parameters $q$ and $0,0$: there is a unit power series $u$ with $F_0$'s $q$-series $u$ times `drinfeldDivisor q 0 0` formed relative to $\bot$ (here the $n$-series is defined by $[0]=0$ and $[n+1]=F_0([n],X)$). Let $T$ be a local commutative $k$-algebra whose maximal ideal has square $\bot$, and let $\mathrm{res}_T : T \to k$ be a ring homomorphism that is a left inverse of the structure map $k \to T$ and whose kernel is the maximal ideal of $T$. Let $G, G'$ be commutative formal group laws over $T$ each reducing to $F_0$, i.e. applying $\mathrm{res}_T$ coefficientwise to $G$, respectively $G'$, gives $F_0$, and suppose the coefficients of $X^q$ in the $q$-series of $G$ and of $G'$ agree. Then there is an isomorphism of formal group laws $\psi : G \to G'$, that is, a power series with zero constant term and unit linear coefficient satisfying $\psi(G(X,Y)) = G'(\psi(X),\psi(Y))$, whose reduction along $\mathrm{res}_T$ is the series $X$: the image of the $m$-th coefficient is $1$ for $m = 1$ and $0$ otherwise.
--
--   This is the injectivity on tangent vectors in Lubin–Tate deformation theory of a formal group law of height two: a first-order deformation of $F_0$ is determined up to isomorphism (rigidly, by an isomorphism reducing to the identity) by the $X^q$-coefficient of its $q$-series. It feeds the existence and uniqueness of classifying homomorphisms from a power series ring over square-zero bases, [`FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries`](thm.html#FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries), and the variant hypothesis version [`FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot`](thm.html#FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra k T]
    (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hres : ∀ a : k, resT (algebraMap k T a) = a) (hker : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) [G.IsComm] [G'.IsComm] (hG : G.IsBaseChange resT F₀) (hG' : G'.IsBaseChange resT F₀)
    (hc : PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q)) :
    ∃ ψ : FormalGroup.LawIso G G', ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0 := by sorry
