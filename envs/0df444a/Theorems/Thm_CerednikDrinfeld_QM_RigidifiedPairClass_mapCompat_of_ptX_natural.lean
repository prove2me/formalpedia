-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_mapCompat_of_ptX_natural
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.mapCompat_of_ptX_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7a6f38c6-6ae7-5d01-9171-814389311ba0
-- title:
--   Push-forward preserves the relation on rigidified presented points
-- statement:
--   Data: a prime $r$, a nonzero $N$ with $r \nmid N$, a prime $\bar r \neq r$; a commutative ring $\mathcal O$ with an element $\pi$ such that $(r) = (\pi)$, and a commutative $\mathcal O$-algebra $\mathcal O^{\mathrm{nr}}$; rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0<a$ or $0<b$, and for a finite place $v$ of $\mathbb Q$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ lies over $r$ or over $\bar r$; a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ which is an order maximal among orders and contains every rational integer; a coordinate map $\mathrm{coord}:\Lambda \to W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord` (additive, unital, Frobenius-twisted multiplicativity, injective, $r$-adically dense, and trace-compatible); a fake elliptic curve $A_0$ of level $N$ with $\Lambda$-action over $\mathcal O^{\mathrm{nr}}/(\pi)$; an integer $n \ge 3$ with $r \nmid n$; a scheme $M$ with $f_M : M \to \operatorname{Spec}\mathcal O$ and a point rule $\mathrm{ptF}$ making $(M,f_M,\mathrm{ptF})$ a fine moduli scheme for fake elliptic curves of level $N$ with full level-$n$ structure; a noetherian $\mathcal O$-algebra $C$ in which the image of $\pi$ is nilpotent, and $\psi : \mathcal O^{\mathrm{nr}} \to_{\mathcal O} C$. Write $M_C$ for the fibre product of $f_M$ with $\operatorname{Spec} C \to \operatorname{Spec}\mathcal O$ and $g$ for its second projection. Given schemes $X d$ with structure morphisms $\xi d : X d \to M_C$, a rule $t_M$ assigning to a full level-$n$ fake elliptic curve over a $C$-algebra $T$ a point of $M_C$ over $\operatorname{Spec} T \to \operatorname{Spec} C$, and a rule $\mathrm{xOf}$ assigning to each $C$- and $\mathcal O$-algebra $T$ in a compatible tower, each $\psi_T = \psi$ followed by $C \to T$, each full level-$n$ object $u$ over $T$ and each rigidification $\rho$ of $u$ relative to $A_0$, a morphism $\operatorname{Spec}(T/(\pi)) \to X \rho.d$ lifting the reduction of $t_M(T,u)$ along $\xi \rho.d$. Assume the hypothesis `hx2`: the derived rule `RigidifiedPairClass.ptX` is natural, namely for $\varphi : T \to_C T'$, compatible $\psi_T$, objects $u,u'$, rigidifications $\rho,\rho'$ of common exponent $d$, and $g : u'.1.A \to u.1.A$ exhibiting $u'.1$ as the pullback of $u.1$ along $\varphi$ compatibly with group law, $\Lambda$-action, level subscheme, the level-$n$ point and the rigidifications, and with $\pi$ zero in $T$ and $T'$, the value of `ptX` at $(T',\rho')$ equals $\operatorname{Spec}\varphi$ followed by its value at $(T,\rho)$. Conclusion: `RigidifiedPairClass.MapCompat` holds for these data, i.e. for all $C$-algebras $T,T'$, every $C$-algebra map $\varphi : T \to T'$ and all $p,q$ in `Pt (algebraMap 𝒪 C π) g X ξ T`, the relation `Rel` between $p$ and $q$ implies `Rel` between their push-forwards $p.map\,\varphi$ and $q.map\,\varphi$, where `Pt.map` composes the $M_C$-point with $\operatorname{Spec}\varphi$, keeps the exponent $d$, and composes the $X d$-point with the map of $\pi$-reductions induced by $\varphi$.
--
--   This supplies the functoriality condition `MapCompat` needed to make the quotient of the presented-point functor by `Rel` into a functor on $C$-algebras, in the Čerednik–Drinfeld description of fake elliptic curves with rigidification near the prime $r$. It is used by [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified), and is proved from base change of full-level fake elliptic curves and of rigidifications together with the assumed naturality of `ptX`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_mapCompat_of_ptX_natural.lean

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

theorem CerednikDrinfeld.QM.RigidifiedPairClass.mapCompat_of_ptX_natural
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

    (hx2 : (∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp ψ)
                (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
                (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
                (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
                (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
                (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
                (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
                FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                  ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                    Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ ((RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0).1)) :
    RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf := by sorry
