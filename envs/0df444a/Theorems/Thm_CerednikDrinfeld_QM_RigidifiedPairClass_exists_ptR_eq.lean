-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.exists_ptR_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7dc0b131-7340-542e-b904-8b5a7ba70634
-- title:
--   Surjectivity of the rigidified-pair point map `ptR`
-- statement:
--   Fix a prime $r$ and $N \neq 0$ with $r \nmid N$, a prime $\bar r \neq r$, a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$, and an $\mathcal O$-algebra $O^{nr}$. Let $a,b \in \mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $a>0$ or $b>0$ and, for a height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completion $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$; let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a maximal order containing all rational integers, equipped with a coordinate map $\mathrm{coord} : \Lambda \to \mathbb W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord`, and let $A_0$ be a fake elliptic curve over $O^{nr}/(\pi)$ for $\Lambda$ and $N$. Fix $n \geq 3$ with $r \nmid n$, a scheme $M$ over $\operatorname{Spec} \mathcal O$ with a point rule $\mathrm{ptF}$ making it a fine moduli scheme for fake elliptic curves with full level $n$ structure, a Noetherian $\mathcal O$-algebra $C$ in which $\pi$ is nilpotent, and $\psi : O^{nr} \to C$. Fix further strata $X_d$ over $M_C = M \times_{\operatorname{Spec}\mathcal O} \operatorname{Spec} C$ with structure maps $\xi_d$, an $M_C$-point rule $t_M$ on $C$-algebras, and a rule $\mathrm{xOf}$ assigning to each $C$- and $\mathcal O$-algebra $T$ in a scalar tower, each $\psi_T$ induced by $\psi$, each full-level object $u$ over $T$ and each rigidification $\rho$ of $u$ (a reduction $E_b$ of $u$ over $T/(\pi)$, a base change $A_b$ of $A_0$, an integer $d$ and a level-preserving pair of isogenies between $E_b$ and $A_b$ composing to $r^d$) a point of $X_{\rho.d}$ over $T/(\pi)$ lying over $t_M(T,u)$; assume the compatibility `MapCompat` for these data, that the $M$-coordinate of $t_M(T,u)$ is always $\mathrm{ptF}$, the hypothesis `hx3` that for each $d$ and each $T$ killing $\pi$ the induced rule $\mathrm{ptX}$ hits every point of $X_d$ over $T$, and the hypothesis `hxOf` that $\mathrm{xOf}$ is natural: for a $C$-algebra map $\varphi : S \to S'$ and pullback-compatible $(u,\rho)$, $(u',\rho')$ one has $\rho'.d = \rho.d$ and the point of $(u',\rho')$ is the pullback along $\varphi$ of that of $(u,\rho)$. The conclusion is that for every $C$- and $\mathcal O$-algebra $S$ in a scalar tower, every $\psi_S$ induced by $\psi$ and every class $z$ in the value at $S$ of the functor `PR` built from these data, there exist a fake elliptic curve with full level $n$ structure $u$ over $S$ and a rigidification $\rho$ of $u$ with $\mathrm{ptR}(S,\psi_S,u,\rho) = z$, where $\mathrm{ptR}$ sends $(u,\rho)$ to the class of the presented point with $M_C$-coordinate $t_M(S,u)$, index $\rho.d$ and stratum coordinate $\mathrm{xOf}(S,\psi_S,u,\rho)$.
--
--   This is the surjectivity half of the statement that the functor `PR` of presented points is the functor of rigidified fake elliptic curves with full level structure in the Čerednik–Drinfeld setting over a $\pi$-nilpotent base. It is used in the proof of [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified), which packages the moduli description of the strata into a representability statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean

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

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_ptR_eq
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
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

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
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ) (z : (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u ρ = z) := by sorry
