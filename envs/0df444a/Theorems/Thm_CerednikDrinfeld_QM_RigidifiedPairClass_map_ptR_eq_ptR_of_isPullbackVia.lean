-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.map_ptR_eq_ptR_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/beab17a5-fb73-5717-8fd0-4e589ae3db8c
-- title:
--   Naturality of the rigidified-pair class under base change
-- statement:
--   Fix natural numbers $r,N$, a commutative ring $\mathcal{O}$ with an element $\pi$, a commutative $\mathcal{O}$-algebra $O^{nr}$, rationals $a,b$, and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ containing every rational integer; fix a fake elliptic curve $A_0$ over $O^{nr}/(\pi)$ with $\Lambda$-action and level-$N$ data, a natural number $n$, a commutative $\mathcal{O}$-algebra $C$, an $\mathcal{O}$-algebra map $\psi:O^{nr}\to C$, a scheme $M_C$ over $\operatorname{Spec} C$ via $g$, schemes $X(d)$ with morphisms $\xi_d:X(d)\to M_C$, an assignment $t_M$ sending a $C$-algebra $T$ and a pair $u=(E,\text{full level-}n\text{ structure})$ over $T$ to a morphism $\operatorname{Spec} T\to M_C$ over $\operatorname{Spec} C$, and an assignment $\mathrm{xOf}$ sending $T$ (also an $\mathcal{O}$-algebra compatibly, with $\psi_T$ the composite of $\psi$ with $C\to T$), a pair $u$ and a rigidification $\rho$ of $u.1$ relative to $A_0$ (a reduction $E_b$ of $E$ mod $\pi$, a curve $A_b$ pulled back from $A_0$, an exponent $d$ and an $r^d$-isogeny pair between them preserving level) to a morphism $\operatorname{Spec}(T/(\pi))\to X(\rho.d)$ whose composite with $\xi_{\rho.d}$ is the reduction of $t_M(T,u)$; let `hmap` be the hypothesis `MapCompat`, compatibility of the relation defining `PR` with base change along $C$-algebra maps. Assume two naturality hypotheses: $t_M$ is natural, i.e. whenever $\varphi:S\to S'$ is a $C$-algebra map, $u,u'$ are pairs over $S,S'$ and $g':u'.1.A\to u.1.A$ exhibits $u'.1$ as pullback of $u.1$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian over $\operatorname{Spec}\varphi$, compatible with the relative group law and the $\Lambda$-action, level points descending) with level sections matching, then $t_M(S',u')=\operatorname{Spec}\varphi$ followed by $t_M(S,u)$; and $\mathrm{xOf}$ is natural, i.e. under the same data together with rigidifications $\rho,\rho'$ related by `Rigidification.IsPullbackVia` (comparison maps of the reductions compatible with $g_b,g_A$ and the isogenies, with $\rho'.d=\rho.d$) there is an equality $h_d:\rho'.d=\rho.d$ for which $\mathrm{xOf}(S',u',\rho')$ transported along $X(h_d)$ equals $\operatorname{Spec}$ of the induced map $S/(\pi)\to S'/(\pi)$ followed by $\mathrm{xOf}(S,u,\rho)$. The conclusion: for such $S,S',\varphi,\psi_S$, pairs $u,u'$, rigidifications $\rho$ over $\psi_S$ and $\rho'$ over $\varphi\circ\psi_S$, comparison $g'$ with `FakeEllipticCurve.IsPullbackVia`, matching level sections and `Rigidification.IsPullbackVia`, the functorial map of `PR` along $\varphi$ carries the class $\mathrm{ptR}(S,\psi_S,u,\rho)$ to the class $\mathrm{ptR}(S',\varphi\circ\psi_S,u',\rho')$.
--
--   This is the functoriality statement for the class map attached to rigidified fake elliptic curves with full level structure: the class of a pair over $S$, pushed forward along a $C$-algebra map, is the class of its pull-back. It is one of the verifications used in constructing a representing functor for the unramified strata of rigidified curves in the Čerednik–Drinfeld setting, and it is also used in the comparison of pairs whose classes agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_map_ptR_eq_ptR_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.RigidifiedPairClass.map_ptR_eq_ptR_of_isPullbackVia
    {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
    {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf)

    (hTnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S')
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (g' : u'.1.A ⟶ u.1.A), FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g' →
      (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
      (tM S' u').1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (tM S u).1)

    (hXnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
      (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
      (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
      (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
      (g' : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g'),
      (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
      FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g' hg ρ ρ' →
        ∃ hd : ρ'.d = ρ.d,
          (xOf S' _ hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1)

    (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
    (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
    (g' : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g')
    (hP : (u'.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1)
    (hρ : FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g' hg ρ ρ') :
    (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).map φ
        (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S ψS hψS u ρ) =
      RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ' := by sorry
