-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_ptR_eq_of_isoVia_of_corr
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.ptR_eq_of_isoVia_of_corr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/40616996-b11a-5a63-9ecc-25d0830f94bd
-- title:
--   Isomorphism invariance of the rigidified-pair class ptR
-- statement:
--   Fix natural numbers $r,N$, a commutative ring $\mathcal O$ with an element $\pi$, a commutative $\mathcal O$-algebra $O_{nr}$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ containing the image of every integer (hypothesis `hΛℤ`), a fake elliptic curve $A_0$ with $\Lambda$-action and level-$N$ data over $O_{nr}/(\pi)$, a natural number $n$, a commutative $\mathcal O$-algebra $C$ and $\psi : O_{nr}\to C$ over $\mathcal O$. Fix the data of the rigidified-pair model: a scheme $M_C$ with $g : M_C \to \operatorname{Spec} C$, schemes $X_d$ with $\xi_d : X_d \to M_C$, a rule $t_M$ assigning to each $C$-algebra $T$ and each $T$-point $u$ of the full-level-$n$ moduli problem (a fake elliptic curve over $T$ together with a full level-$n$ structure) a morphism $\operatorname{Spec} T \to M_C$ over $g$, a rule $\mathrm{xOf}$ assigning to each such $u$ over a compatible $\mathcal O$- and $C$-algebra $T$ and each rigidification $\rho$ of $u.1$ relative to $A_0$ (a reduction $\rho.E_b$ over $T/(\pi)$ pulled back from $u.1$, a curve $\rho.A_b$ pulled back from $A_0$, an exponent $\rho.d$ and an isogeny pair of degree $r^{\rho.d}$ between them preserving the level) a morphism $\operatorname{Spec}(T/(\pi)) \to X_{\rho.d}$ lifting the reduction of $t_M(T,u)$ along $\xi_{\rho.d}$, and the compatibility `hmap` of the relation defining the quotient with base change. Assume moreover: $t_M$ takes the same value on $u$ and $u'$ whenever they are related by an isomorphism $i$ of the underlying curves over the base satisfying `WithFullLevel.IsoVia`, i.e. $i$ respects the relative group laws, intertwines the $\Lambda$-actions, matches the level subschemes and carries the marked point $u.2.P$ to $u'.2.P$; and $\mathrm{xOf}$ is natural (`hXnat`): for $\varphi : S \to S'$ over $C$ and $\mathcal O$-compatible, points $u$ over $S$, $u'$ over $S'$ with $g' : u'.1.A \to u.1.A$ exhibiting $u'$ as the pullback of $u$ and respecting the marked points, and rigidifications $\rho,\rho'$ related by `Rigidification.IsPullbackVia`, one has $\rho'.d = \rho.d$ and the square relating $\mathrm{xOf}(S',u',\rho')$ and $\mathrm{xOf}(S,u,\rho)$ over $\mathrm{qmap}$ commutes. Then, for $S$ a compatible $\mathcal O$- and $C$-algebra with $\psi_S$ factoring $\psi$, for $u,u'$ over $S$ with rigidifications $\rho,\rho'$, an isomorphism $i : u.1.A \cong u'.1.A$ over $S$ satisfying `WithFullLevel.IsoVia`, and assuming the correspondence hypothesis `hcorr`: there exist $i_b : \rho.E_b.A \to \rho'.E_b.A$ compatible with the maps $\rho.g_b,\rho'.g_b$ and with the structure morphisms, a morphism $u_A : \rho'.A_b.A \to \rho.A_b.A$ exhibiting $\rho'.A_b$ as the pullback of $\rho.A_b$ along the identity and compatible with $\rho.g_A,\rho'.g_A$, and exponents $i_1,j_1$ with $i_b$ followed by $\rho'.\varphi$, $u_A$ and the action of $r^{i_1}$ equal to $\rho.\varphi$ followed by the action of $r^{j_1}$ — then the two classes $\mathrm{ptR}$ of $(u,\rho)$ and of $(u',\rho')$ in the quotient $\mathrm{PR}$ evaluated at $S$ coincide.
--
--   This is the isomorphism-invariance step for the class map attached to the rigidified-pair model: it shows that the functor-valued invariant $\mathrm{ptR}$ depends only on the isomorphism class of a pair (fake elliptic curve with full level structure, rigidification), up to correspondences differing by $r$-power scalars. It is used in the representability statement [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified) and is paired with its converse [`CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem`](thm.html#CerednikDrinfeld.QM.RigidifiedPairClass.exists_isoVia_corr_of_ptR_eq_of_forall_isIdempotentElem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_ptR_eq_of_isoVia_of_corr.lean

import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.RigidifiedPairClass.ptR_eq_of_isoVia_of_corr
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

    (hTiso : ∀ (S : Type) [CommRing S] [Algebra C S] (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
      (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
      (tM S u).1 = (tM S u').1)

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

    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hiso : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
    (hcorr : ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
        (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
        (i₁ j₁ : ℕ),
        ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S ψS hψS u ρ =
      RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap S ψS hψS u' ρ' := by sorry
