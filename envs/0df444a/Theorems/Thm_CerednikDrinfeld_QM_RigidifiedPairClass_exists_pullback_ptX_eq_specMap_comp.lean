-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_pullback_ptX_eq_specMap_comp
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.exists_pullback_ptX_eq_specMap_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/ebc8ec56-644e-5b4d-b86d-568178293150
-- title:
--   Base change of rigidified pairs; naturality of `ptX`
-- statement:
--   Fix the Čerednik–Drinfeld frame: primes $r \ne \bar r$ and $N \neq 0$ with $r \nmid N$; a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$; a commutative $\mathcal O$-algebra $O^{nr}$; rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, at each finite place $v$ of $\mathbb Q$, is a division algebra over the completion exactly when $v$ lies above $r$ or $\bar r$; a maximal order $\Lambda$ (an order: containing $1$, closed under multiplication, spanning over $\mathbb Q$, finitely generated, maximal among the orders containing it) containing all integers; a coordinate map $\mathrm{coord}:\Lambda\to\mathbb Z_{r^2}\times\mathbb Z_{r^2}$ satisfying `IsOrderCoord` (additive, $1 \mapsto (1,0)$, the Frobenius-twisted multiplication rule, injective, dense, and the trace identity); a fake elliptic curve $A_0$ over $O^{nr}/(\pi)$; a level $n\ge 3$ with $r \nmid n$; a scheme $M$ over $\operatorname{Spec}\mathcal O$ with a point rule $\mathrm{ptF}$ making it a fine moduli scheme for fake elliptic curves with full level-$n$ structure (isomorphism-invariant, compatible with base change, surjective and injective up to isomorphism); a Noetherian $\mathcal O$-algebra $C$ in which $\pi$ becomes nilpotent, a leg $\psi : O^{nr}\to_{\mathcal O} C$; degree strata $X_d$ with maps $\xi_d$ to $M\times_{\operatorname{Spec}\mathcal O}\operatorname{Spec} C$, a point rule $t_M$ for curves with full level over $C$-algebras, and a rule $\mathrm{xOf}$ which to a $C$-algebra $T$ carrying a compatible $\mathcal O$-structure, a leg $\psi_T$ factoring $\psi$ through $C\to T$, a curve with full level $u$ over $T$ and a rigidification $\rho$ of $u.1$ along $\psi_T$ assigns a morphism $\operatorname{Spec}(T/(\pi))\to X_{\rho.d}$ lying, after $\xi_{\rho.d}$, over the reduction modulo $\pi$ of $(t_M\,T\,u)$. Assume $\mathrm{xOf}$ is natural: for every $C$-algebra map $\varphi : S\to S'$ and every pair $(u,\rho)$, $(u',\rho')$ linked by a morphism $g$ exhibiting $u'.1$ as base change of $u.1$ along $\varphi$, compatibly with the full-level sections and with the rigidifications, one has $\rho'.d=\rho.d$ and the two stratum points agree after the induced map of quotients. The conclusion asserts the existence of such data: for all $S,S'$, $\varphi : S\to_C S'$, a leg $\psi_S$ factoring $\psi$, $u$ over $S$ and a rigidification $\rho$ of $u.1$ along $\psi_S$, there exist a factorisation proof for $\varphi\circ\psi_S$, a curve with full level $u'$ over $S'$, a rigidification $\rho'$ of $u'.1$ along $\varphi\circ\psi_S$, a morphism $g : u'.1.A\to u.1.A$ making $u'.1$ the base change of $u.1$ along $\varphi$ (cartesian square, compatible with the group laws, $\Lambda$-equivariant, carrying level structures), compatibility of the full-level sections, a pull-back relation of $\rho$ and $\rho'$, and an equality $\rho'.d=\rho.d$, such that whenever $\pi$ maps to $0$ in both $S$ and $S'$ the point `ptX` at degree $\rho.d$ attached to $(S',u',\rho')$ equals $\operatorname{Spec}\varphi$ followed by the point `ptX` attached to $(S,u,\rho)$.
--
--   This is the base-change step for rigidified fake elliptic curves with full level structure in the presented-point model of rigidified-pair classes: pull-backs of the curve, its level structure and its rigidification exist along any map of $C$-algebras, the degree $d$ is unchanged, and the resulting point of the degree stratum $X_d$ is natural. It is used in the local-to-global comparison of rigidified-pair classes, where a rigidified pair must be restricted to the members of a cover and to the reduction modulo $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_pullback_ptX_eq_specMap_comp.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_pullback_ptX_eq_specMap_comp
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
      ∃ (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g)
        (_ : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1)
        (_ : FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ')
        (hd : ρ'.d = ρ.d),
        ∀ (h0 : algebraMap C S (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C S' (algebraMap 𝒪 C π) = 0),
          ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ.d S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ' hd h0').1 =
            Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) ρ.d S ψS hψS u ρ rfl h0).1 := by sorry
