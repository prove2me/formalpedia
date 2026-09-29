-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/462f44b6-f8ba-5c3b-9ebb-3d4c683615bc
-- title:
--   Descent of an isogeny pair along a pullback
-- statement:
--   Fix $N \in \mathbb{N}$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, a field $k_0$ and a fake elliptic curve $A_0$ of level $N$ for $\Lambda$ over $k_0$ (a smooth proper morphism $A_0.f : A_0.A \to \operatorname{Spec} k_0$ with connected fibres of dimension $2$, a commutative relative group law $A_0.L$ on its points over $\operatorname{Spec} k_0$, a multiplicative $\Lambda$-action `act` by endomorphisms over the base satisfying the trace condition, together with the level data). Let $Bb$ be a commutative ring, $\psi_b : k_0 \to Bb$ a ring homomorphism, $Ab$ a fake elliptic curve for $\Lambda$ of level $N$ over $Bb$, and $g_A : Ab.A \to A_0.A$ a morphism making $Ab$ a pullback of $A_0$ along $\psi_b$ in the sense of `IsPullbackVia`: the square formed by $g_A$, $Ab.f$, $A_0.f$ and $\operatorname{Spec}\psi_b$ is cartesian, composition with $g_A$ carries the group law of $Ab$ on $T$-points to that of $A_0$, one has $Ab.\mathrm{act}\,x$ followed by $g_A$ equal to $g_A$ followed by $A_0.\mathrm{act}\,x$ for every $x \in \Lambda$, and points of $Ab$ factoring through $Ab.\mathrm{lev}$ have their composite with $g_A$ factoring through $A_0.\mathrm{lev}$. Assume further the cancellation hypothesis `huniq`: any two endomorphisms $\chi,\chi'$ of $A_0.A$ over $A_0.f$ that are homomorphisms for $A_0.L$ on $T$-points, for all $T$, and satisfy $g_A \circ$-precomposition equality ($g_A$ followed by $\chi$ equals $g_A$ followed by $\chi'$) are equal. Let $d \in \mathbb{N}$ and let $\varphi,\psi$ be endomorphisms of $Ab.A$ forming an isogeny pair of degree $d$ on $Ab$ in the sense of `IsIsogenyPair` (both lie over $Bb$, are homomorphisms for the group law on points, commute with the $\Lambda$-action, and, whenever the image of $d$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, their two composites equal $Ab.\mathrm{act}\,d$). Let $\varphi_0,\psi_0$ be endomorphisms of $A_0.A$ with $\varphi_0 \circ$, $\psi_0 \circ$ lying over $A_0.f$ and satisfying the homomorphism property for $A_0.L$ on $T$-points, and suppose $\varphi$ followed by $g_A$ equals $g_A$ followed by $\varphi_0$, and likewise for $\psi,\psi_0$. Then $(\varphi_0,\psi_0)$ is an isogeny pair of degree $d$ on $A_0$: both are group-law homomorphisms over $k_0$, each commutes with $A_0.\mathrm{act}\,x$ for every $x \in \Lambda$, and if the image of $d$ lies in $\Lambda$ then $\varphi_0$ followed by $\psi_0$ and $\psi_0$ followed by $\varphi_0$ both equal $A_0.\mathrm{act}\,d$.
--
--   This is the descent step for isogeny pairs on fake elliptic curves: relations holding between endomorphisms of a base-changed fake elliptic curve descend to the original curve once the endomorphisms themselves are known to descend and descent of group-law endomorphisms is unique. It is used in the construction of the endomorphism realising the required idempotent on a fake elliptic curve over an algebraically closed field in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {k₀ : Type} [Field k₀] (A₀ : FakeEllipticCurve Λ N k₀)
    {Bb : Type} [CommRing Bb] (ψb : k₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)

    (huniq : ∀ (χ χ' : A₀.A ⟶ A₀.A) (hχ : χ ≫ A₀.f = A₀.f) (hχ' : χ' ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ hχ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ' hχ' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ' hχ' P) (mapPt χ' hχ' Q)) →
      gA ≫ χ = gA ≫ χ' → χ = χ')
    (d : ℕ) (φ ψ : Ab.A ⟶ Ab.A) (hpair : FakeEllipticCurve.IsIsogenyPair d Ab Ab φ ψ)
    (φ₀ ψ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f) (hψ₀ : ψ₀ ≫ A₀.f = A₀.f)
    (hφ₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt φ₀ hφ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (hψ₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt ψ₀ hψ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ₀ hψ₀ P) (mapPt ψ₀ hψ₀ Q))
    (hφg : φ ≫ gA = gA ≫ φ₀) (hψg : ψ ≫ gA = gA ≫ ψ₀) :
    FakeEllipticCurve.IsIsogenyPair d A₀ A₀ φ₀ ψ₀ := by sorry
