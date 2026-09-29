-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_isPullback_levelIff_of_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/637f7a8f-bb0b-558d-99ce-daced1692dce
-- title:
--   Cancellation of cartesian base changes along a composite ring map
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and $N\in\mathbb{N}$. Let $\sigma:S_1\to S_2$ and $\tau:S_2\to S_3$ be ring homomorphisms between commutative rings, and let $E_1,E_2,E_3$ be fake elliptic curves of type $(\Lambda,N)$ over $S_1,S_2,S_3$ respectively (each carrying an abelian scheme $E_i.f:E_i.A\to\operatorname{Spec}S_i$ with relative group law $E_i.L$, a $\Lambda$-action $E_i.act$ and a level morphism $E_i.\mathrm{lev}:E_i.C\to E_i.A$). Assume given $g:E_2.A\to E_1.A$ making the square with $E_2.f$, $E_1.f$ and $\operatorname{Spec}\sigma$ cartesian, such that (i) for every scheme $T$ with structure morphism $t'$ to $\operatorname{Spec}S_2$ and all $T$-points $P,Q$ of $E_2.A$ over $t'$, composing their product with $g$ gives the $E_1$-product over $t'$ followed by $\operatorname{Spec}\sigma$ of $P$ followed by $g$ and $Q$ followed by $g$; (ii) $E_2.act\,x$ followed by $g$ equals $g$ followed by $E_1.act\,x$ for all $x\in\Lambda$; (iii) a point $P$ factors through $E_2.\mathrm{lev}$ if and only if $P$ followed by $g$ factors through $E_1.\mathrm{lev}$. Assume the same data and properties for some $g':E_3.A\to E_1.A$ cartesian over $\operatorname{Spec}(\tau\circ\sigma)$. Then there exists $h:E_3.A\to E_2.A$ with $h$ followed by $g$ equal to $g'$, cartesian over $\operatorname{Spec}\tau$, and satisfying the analogues of (i), (ii), (iii) relative to $E_3$, $E_2$ and $\tau$.
--
--   This is the cancellation step for cartesian (and group-law, $\Lambda$-equivariance and level preserving) base-change data of fake elliptic curves along a factorisation $S_1\to S_2\to S_3$: from compatible comparison morphisms over $\sigma$ and over $\tau\circ\sigma$ it produces the connecting morphism over $\tau$ together with the factorisation $h$ followed by $g$ equals $g'$. It is used in the descent of a fake elliptic curve to a finitely generated subalgebra, where a datum must be re-based along an enlargement of finitely generated subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_isPullback_levelIff_of_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S₁ S₂ S₃ : Type} [CommRing S₁] [CommRing S₂] [CommRing S₃] (σ : S₁ →+* S₂) (τ : S₂ →+* S₃)
    (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂) (E₃ : FakeEllipticCurve Λ N S₃)
    (g : E₂.A ⟶ E₁.A) (hg : CategoryTheory.IsPullback g E₂.f E₁.f (Spec.map (CommRingCat.ofHom σ)))
    (h₁₂ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' E₂.f),
        (E₂.L.mul t' P Q).1 ≫ g =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₂.act x ≫ g = g ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        FactorsThrough E₂.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) → FactorsThrough E₂.lev P))
    (g' : E₃.A ⟶ E₁.A) (hg' : CategoryTheory.IsPullback g' E₃.f E₁.f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
    (h₁₃ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ g' =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (τ.comp σ)))
            ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ g' = g' ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') → FactorsThrough E₃.lev P)) :
    ∃ (h : E₃.A ⟶ E₂.A) (_ : h ≫ g = g') (hh : CategoryTheory.IsPullback h E₃.f E₂.f (Spec.map (CommRingCat.ofHom τ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ h =
          (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom τ))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ h = h ≫ E₂.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) → FactorsThrough E₃.lev P) := by sorry
