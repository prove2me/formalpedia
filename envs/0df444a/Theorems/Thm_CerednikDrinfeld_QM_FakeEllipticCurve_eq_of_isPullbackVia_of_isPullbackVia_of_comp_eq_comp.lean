-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/d2ae2217-0edf-5633-8f2c-fcec2013b261
-- title:
--   Rigidity: pull-back realisations over an Artinian local base coincide
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $\bar k$ be a field, let $B$ be an Artinian local commutative ring and let $\rho\colon B\to\bar k$ be a surjective ring homomorphism with kernel the maximal ideal of $B$. Let $E_0$ be a fake elliptic curve of level data $(\Lambda,N)$ over $\bar k$ and $E'$ one over $B$, and let $g'\colon E_0.A\to E'.A$ satisfy `IsPullbackVia` for $\rho$: the square formed by $g'$, $E_0.f$, $E'.f$ and $\operatorname{Spec}\rho$ is cartesian, composition with $g'$ turns the relative group law of $E_0$ on $T$-points into that of $E'$, $g'$ intertwines the $\Lambda$-actions, and any $T$-point of $E_0$ factoring through its level curve has image under $g'$ factoring through $E'.C$. Let $S$ be a commutative ring, $E$ a fake elliptic curve of the same level data over $S$, and $\varphi\colon S\to B$ a ring homomorphism. If $h,h'\colon E'.A\to E.A$ both satisfy `IsPullbackVia` for $\varphi$ in the same three-fold sense, and $h$ and $h'$ become equal after precomposition with $g'$, then $h=h'$.
--
--   This is the rigidity statement underlying uniqueness in the deformation theory of fake elliptic curves: a map exhibiting $E'$ as the pull-back of $E$ along $\varphi$ is determined by its restriction to the special fibre over the residue field. It is used in the construction of the formal module of the Čerednik–Drinfeld setting, both for the uniqueness of pull-backs along power-series towers and for the comparison of two pull-back presentations along a pushout square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (kbar : Type) [Field kbar]
    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (ρ : B →+* kbar) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = maximalIdeal B)
    (E₀ : FakeEllipticCurve Λ N kbar) (E' : FakeEllipticCurve Λ N B)
    (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g')
    (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) (φ : S →+* B)
    (h h' : E'.A ⟶ E.A)
    (hh : FakeEllipticCurve.IsPullbackVia φ E E' h) (hh' : FakeEllipticCurve.IsPullbackVia φ E E' h')
    (hcomp : g' ≫ h = g' ≫ h') :
    h = h' := by sorry
