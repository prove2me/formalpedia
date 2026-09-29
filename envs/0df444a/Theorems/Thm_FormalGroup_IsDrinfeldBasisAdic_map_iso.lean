-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_iso
-- name    : FormalGroup.IsDrinfeldBasisAdic.map_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/db45c78a-9a1b-5f50-9a36-5e6dea88d07d
-- title:
--   Adic Drinfeld bases transport along isomorphisms of formal groups
-- statement:
--   Let $T$ be a commutative ring and $I \subseteq T$ an ideal for which $T$ is $I$-adically complete. Let $F$ and $G$ be one-dimensional formal group laws over $T$ and let $\varphi$ be an isomorphism $F \to G$ of such laws, i.e. a power series $\varphi$ with zero constant term satisfying the homomorphism identity $\varphi(F(X_0,X_1)) = G(\varphi(X_0),\varphi(X_1))$ and with $\mathrm{coeff}_1(\varphi)$ a unit of $T$. Let $q$ be a natural number and let $x_0, x_1$ be elements of $I$. Assume $F$ satisfies `IsDrinfeldBasisAdic` for $I$, $q$, $x_0$, $x_1$: reading the topology/ideal data on $T$ as that given by $I$, there is a unit $u$ of $\mathrm{PowerSeries}\ T$ with $F.\mathrm{nthSeries}\ q = u \cdot F.\mathrm{drinfeldDivisor}\ q\ x_0\ x_1$, that is, the $q$-division series of $F$ agrees with the Drinfeld divisor attached to $(x_0,x_1)$ up to a unit factor. The conclusion is the same assertion for $G$, at the same $q$ and at the two points obtained by evaluating $\varphi$ adically at $x_0$ and at $x_1$ (`φ.toLawHom.appAdic I`): there is a unit $v$ with $G.\mathrm{nthSeries}\ q = v \cdot G.\mathrm{drinfeldDivisor}\ q\ (\varphi(x_0))\ (\varphi(x_1))$.
--
--   This is the transport of Drinfeld level-$q$ basis conditions on the formal group of a curve along an isomorphism of formal group laws, in the adically complete setting. It is used to compare Drinfeld level structures attached to different but isomorphic formal models, and is invoked in the construction of points on modular curves with prescribed level data and in the description of the maximal ideal cut out by an adic Drinfeld basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_map_iso.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.map_iso
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F G : FormalGroup T) (φ : FormalGroup.LawIso F G)
    (q : ℕ) (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (h : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    G.IsDrinfeldBasisAdic I q (φ.toLawHom.appAdic I x₀) (φ.toLawHom.appAdic I x₁) := by sorry
