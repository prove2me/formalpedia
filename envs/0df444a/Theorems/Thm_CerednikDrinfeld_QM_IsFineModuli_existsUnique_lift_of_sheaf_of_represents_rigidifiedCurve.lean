-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve
-- name    : CerednikDrinfeld.QM.IsFineModuli.existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/71b22c9d-594c-560f-b540-ff6d762960eb
-- title:
--   Formal étaleness of the rigidified-curve functor over the fine moduli scheme
-- statement:
--   Fix a prime $r$, an $N$ with $r \nmid N$, and a prime $\bar r \neq r$; a commutative ring $\mathcal O$ with an element $\pi$ generating the same ideal as $r$, and an $\mathcal O$-algebra $Onr$. Let $\mathbb H[\mathbb Q,a,b]$ be indefinite (i.e. $0<a$ or $0<b$) and nonsplit at exactly the places above $r$ and $\bar r$, let $\Lambda$ be a maximal order containing all rational integers, let $coord$ be a coordinate map $\Lambda \to \mathbb Z_{p^2}\times\mathbb Z_{p^2}$ satisfying `IsOrderCoord` (additive, unital, twisted-multiplicative, injective, dense, trace-compatible), and let $A_0$ be a fake elliptic curve with $\Lambda$-action and level-$N$ structure over $Onr/\pi$. Fix $n \ge 3$ with $r \nmid n$ and a scheme $M$ over $\mathrm{Spec}\,\mathcal O$ with point rule $ptF$ which is a fine moduli space for fake elliptic curves with full level $n$ (isomorphism invariance, pull-back compatibility, surjectivity and injectivity of $ptF$). Let $C$ be a Noetherian $\mathcal O$-algebra in which $\pi$ is nilpotent, with an $\mathcal O$-algebra map $\psi : Onr \to C$. Let $PR$ be a functor on $C$-algebras, $ptR$ a rule assigning to each full-level-$n$ curve $u$ over a $C$-algebra $S$ together with a rigidification $\rho$ of $u$ relative to $A_0$ and $\pi$ an element of $PR(S)$, and $toM$ a map from $PR(S)$ to $S$-points of the base change of $M$ to $C$. Assume: $PR$ satisfies the Zariski sheaf condition for finite families of away-localisations generating the unit ideal; $toM$ is natural in $S$; $ptR$ is invariant under isomorphisms of full-level curves compatible with the rigidification data up to powers of $r$; $ptR$ commutes with pull-back along $C$-algebra maps; $ptR$ is surjective; $ptR$ is injective up to such isomorphisms over bases with no nontrivial idempotents; and $toM \circ ptR$ agrees with $ptF$. Then for every square-zero surjection $p : S \to S_0$ of $C$-algebras with $S$ Noetherian, every $x_0 \in PR(S_0)$ and every $S$-point $t$ of the base-changed moduli scheme whose restriction along $p$ equals $toM(x_0)$, there is a unique $x \in PR(S)$ with $PR(p)(x) = x_0$ and $toM(x) = t$.
--
--   This is the formal étaleness (infinitesimal lifting with uniqueness) of the functor of rigidified fake elliptic curves over the $\pi$-adic fine moduli scheme, deduced purely from the sheaf property and the point-rule axioms for $ptR$ and $toM$. It is the étale-ness input to the construction of the representing functor used in the Cerednik–Drinfeld uniformisation of Shimura curves, and is cited by [`CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_algFunctor_represents_rigidifiedCurve_strata_unramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsFineModuli.existsUnique_lift_of_sheaf_of_represents_rigidifiedCurve
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
    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 → PR.obj S)
    (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
      PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (hsh :
      (∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
        Ideal.span (Set.range f) = ⊤ →
        ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
          [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
        (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
            [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
            PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
        ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i))
    (hR0 :
      (∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
          (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1))
    (hR1 :
      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ'))
    (hR2 :
      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ'))
    (hR3s :
      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ) (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z))
    (hR3i :
      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hR4 :
      (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
          (toM S (ptR S ψS hψS u ρ)).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
            (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)) :
    ∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
      Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
      ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
      Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
      ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t := by sorry
