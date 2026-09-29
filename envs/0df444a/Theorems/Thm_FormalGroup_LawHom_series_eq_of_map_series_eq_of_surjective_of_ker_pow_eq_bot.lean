-- Prove2me | Theorems.Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
-- name    : FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/205cef39-e740-5505-ab55-da6809b7b769
-- title:
--   Rigidity of homomorphisms between nilpotent-kernel lifts
-- statement:
--   Let $q$ be a prime, $T$ a commutative ring, $k$ a field of characteristic $q$, and $\pi : T \to k$ a surjective ring homomorphism. Assume that for some $n$ the $n$-th power of $\ker \pi$ is the zero ideal and that $q^n = 0$ in $T$. Let $F_0$ be a commutative one-dimensional formal group law over $k$ which satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with respect to the zero ideal of $k$ its $q$-series $F_0$-multiplication-by-$q$ power series is a unit power series times `F₀.drinfeldDivisor q 0 0`; by the cited characterisation [`FormalGroup.isDrinfeldBasisAdic_zero_zero_iff`](thm.html#FormalGroup.isDrinfeldBasisAdic_zero_zero_iff) this says that `F₀.nthSeries q` is a unit times $X^{q\cdot q}$, i.e. $F_0$ has height two. Let $G, G'$ be formal group laws over $T$ with $G'$ commutative, both lifting $F_0$ in the sense that applying $\pi$ coefficientwise to the two-variable power series of $G$, respectively of $G'$, gives that of $F_0$. Finally let $\psi_1, \psi_2$ be homomorphisms $G \to G'$ of formal group laws, each given by a power series over $T$ with zero constant term which intertwines $G$ and $G'$ under substitution. If the images of the two series under $\pi$ coincide, then the two series are equal.
--
--   This is the rigidity statement underlying uniqueness in Lubin–Tate deformation theory: a homomorphism between two lifts, along a nilpotent-kernel surjection, of a height-two commutative formal group law in characteristic $q$ is determined by its reduction. It is used in the inductive construction of classifying maps along small extensions, in particular by [`FormalGroup.IsDrinfeldBasisAdic.algHom_eq_of_smallExtension_of_sqZero`](thm.html#FormalGroup.IsDrinfeldBasisAdic.algHom_eq_of_smallExtension_of_sqZero), [`FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_isBaseChange_lawIso`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_isBaseChange_lawIso) and [`FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X`](thm.html#FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
    (q : ℕ) [Fact q.Prime] {T k : Type*} [CommRing T] [Field k] [CharP k q]
    (π : T →+* k) (hπs : Function.Surjective π) (n : ℕ) (hπ : RingHom.ker π ^ n = ⊥) (hqn : (q : T) ^ n = 0)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (G G' : FormalGroup T) [G'.IsComm] (hG : G.IsBaseChange π F₀) (hG' : G'.IsBaseChange π F₀)
    (ψ₁ ψ₂ : FormalGroup.LawHom G G')
    (h : PowerSeries.map π ψ₁.series = PowerSeries.map π ψ₂.series) :
    ψ₁.series = ψ₂.series := by sorry
