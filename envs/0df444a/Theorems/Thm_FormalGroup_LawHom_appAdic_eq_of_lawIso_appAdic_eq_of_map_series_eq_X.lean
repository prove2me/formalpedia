-- Prove2me | Theorems.Thm_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
-- name    : FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/3cacdee6-8233-51bd-9ceb-979f076f46d7
-- title:
--   Transport of adic parameters along a homomorphism reducing to X
-- statement:
--   Let $q$ be a prime, let $T$ be a commutative local Artinian ring and $k$ a field of characteristic $q$, and let $\mathrm{res} : T \to k$ be a surjective ring homomorphism whose kernel is the maximal ideal of $T$. Let $F_0$ be a commutative formal group law over $k$ satisfying `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. (relative to the ideal $\bot$ of $k$) the series `F₀.nthSeries q` is a unit power series times `F₀.drinfeldDivisor q 0 0`. Let $F_1, F_2, G$ be formal group laws over $T$ with $G$ commutative, such that $F_0$ is the reduction along $\mathrm{res}$ of both $F_1$ and $G$ (their two-variable power series map to that of $F_0$). Let $\psi_1 : F_1 \to G$ and $\psi_2 : F_2 \to G$ be law isomorphisms, that is one-variable power series with zero constant coefficient and unit linear coefficient satisfying the homomorphism identity, and assume each has all coefficients reducing along $\mathrm{res}$ to those of $X$. Let $\sigma : F_1 \to F_2$ be a law homomorphism whose series also reduces to $X$. Finally let $a_1, a_2$ lie in the maximal ideal $\mathfrak m$ of $T$ and suppose the $\mathfrak m$-adic evaluations agree: $\psi_1(a_1) = \psi_2(a_2)$. Then the $\mathfrak m$-adic evaluation of $\sigma$ at $a_1$ equals $a_2$.
--
--   A rigidity statement for formal group laws over an Artinian local base: homomorphisms and isomorphisms reducing to the identity series are determined by their reductions, so that a point matched by two such isomorphisms is transported by the unique homomorphism between the sources. It is used in the level-transport lemmas [`ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow) and [`ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
    (q : ℕ) [Fact q.Prime] {T k : Type u} [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Field k] [CharP k q]
    (res : T →+* k) (hres : Function.Surjective res) (hker : RingHom.ker res = maximalIdeal T)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (F₁ F₂ G : FormalGroup T) [G.IsComm] (hF₁ : F₁.IsBaseChange res F₀) (hG : G.IsBaseChange res F₀)
    (ψ₁ : FormalGroup.LawIso F₁ G) (ψ₂ : FormalGroup.LawIso F₂ G)
    (hψ₁ : ∀ n : ℕ, res (PowerSeries.coeff n ψ₁.series) = if n = 1 then 1 else 0)
    (hψ₂ : ∀ n : ℕ, res (PowerSeries.coeff n ψ₂.series) = if n = 1 then 1 else 0)
    (σ : FormalGroup.LawHom F₁ F₂) (hσ : PowerSeries.map res σ.series = PowerSeries.X)
    (a₁ a₂ : T) (ha₁ : a₁ ∈ maximalIdeal T) (ha₂ : a₂ ∈ maximalIdeal T)
    (h : ψ₁.toLawHom.appAdic (maximalIdeal T) a₁ = ψ₂.toLawHom.appAdic (maximalIdeal T) a₂) :
    σ.appAdic (maximalIdeal T) a₁ = a₂ := by sorry
