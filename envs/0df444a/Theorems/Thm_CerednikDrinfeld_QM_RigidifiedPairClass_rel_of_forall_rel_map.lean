-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_of_forall_rel_map
-- name    : CerednikDrinfeld.QM.RigidifiedPairClass.rel_of_forall_rel_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/819dc4b3-90a2-5834-8e52-836d28cf7e19
-- title:
--   Zariski-locality of the rigidified-pair relation over the base
-- statement:
--   Fix a prime $r$, a nonzero $N$ with $r \nmid N$, and a prime $\bar r \neq r$; a commutative ring $\mathcal{O}$ with an element $\pi$ such that $(r) = (\pi)$ in $\mathcal{O}$, and an $\mathcal{O}$-algebra $O^{nr}$. Let $a, b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order containing all integers, equipped with a coordinate map $\mathrm{coord} : \Lambda \to \mathbb{W}(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the twisted rule, injective, with dense image and the prescribed trace identity), and let $A_0$ be a fake elliptic curve over $O^{nr}/(\pi)$. Let $n \geq 3$ with $r \nmid n$, and let $(M, f_M, \mathrm{ptF})$ be a fine moduli datum for fake elliptic curves with $\Lambda$-action, level $N$ and full level $n$ over $\mathcal{O}$. Let $C$ be a Noetherian $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, $\psi : O^{nr} \to C$ an $\mathcal{O}$-algebra map, $X : \mathbb{N} \to \mathbf{Sch}$ a family of strata with structure morphisms $\xi_d$ to $M \times_{\mathcal{O}} C$, $\mathrm{tM}$ the induced point rule over $C$-algebras, and $\mathrm{xOf}$ the rule assigning to a full-level object $u$ over a $C$-algebra $T$ and a rigidification $\rho$ of $u$ relative to $A_0$ a section of $X_{\rho.d}$ over $\operatorname{Spec}(T/(\pi))$ lifting the reduction of $\mathrm{tM}\,T\,u$. Let $A$ be a $C$-algebra, $f_0, \dots, f_{m-1} \in A$ generate the unit ideal, and let $B_i$ be $C$-algebras that are localisations of $A$ away from $f_i$ in the tower $C \to A \to B_i$. Then for presented points $p, q$ over $A$ (each a section of $M \times_{\mathcal{O}} C$ over $A$, an exponent $d$, and a morphism $\operatorname{Spec}(A/(\pi)) \to X_d$ compatible with $\xi_d$), if the images of $p$ and $q$ in each $B_i$ satisfy the relation `Rel` — equality of the moduli sections together with the Zariski-local existence, on a basic open cover of the reduction, of full-level objects with rigidifications of the prescribed degrees, an isomorphism between them, and an identity matching the two rigidifications up to multiplication by powers of $r$, presenting the respective stratum points — then $p$ and $q$ satisfy `Rel` over $A$ itself.
--
--   This is the descent step showing that the equivalence used to define rigidified-pair classes in the Čerednik–Drinfeld uniformisation of Shimura curves is local on the base in the Zariski topology: the moduli sections glue because they agree on a basic open cover, and the local presentations over the $B_i$ refine to a single basic open cover of $\operatorname{Spec}(A/(\pi))$. It is used in the uniqueness statement [`CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top`](thm.html#CerednikDrinfeld.QM.RigidifiedPairClass.PR.existsUnique_map_eq_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_rel_of_forall_rel_map.lean

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

theorem CerednikDrinfeld.QM.RigidifiedPairClass.rel_of_forall_rel_map
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

    (A : Type) [CommRing A] [Algebra C A] (m : ℕ) (f : Fin m → A) (hf : Ideal.span (Set.range f) = ⊤)
    (B : Fin m → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C A (B i)]
    [∀ i, IsLocalization.Away (f i) (B i)]
    (p q : RigidifiedPairClass.Pt (algebraMap 𝒪 C π) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ A)
    (h : ∀ i, RigidifiedPairClass.Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf (B i)
      (p.map (IsScalarTower.toAlgHom C A (B i))) (q.map (IsScalarTower.toAlgHom C A (B i)))) :
    RigidifiedPairClass.Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf A p q := by sorry
