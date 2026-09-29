-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/77faa3e4-27dc-58da-988f-48a6cc9ba5c3
-- title:
--   Localising a noetherian base at the contraction of mathfrak m_R
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ which is a maximal order (an order maximal among orders), and a natural number $N$. Let $T$ be a noetherian commutative ring, $R$ a local commutative ring, and $\varphi : T \to R$ an injective ring homomorphism. Let $E_T$ be a fake elliptic curve over $T$ and $E$ one over $R$ in the project's sense: a scheme with a structure morphism to the spectrum of the base, a commutative relative group law on its functor of points, an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base satisfying additivity, multiplicativity, and a trace condition, together with the level-$N$ data. Let $g : E.A \to E_T.A$ be a morphism making the square with the structure morphisms and $\operatorname{Spec}\varphi$ cartesian, such that for every scheme $X$, every $t' : X \to \operatorname{Spec} R$ and all sections $P,Q$ of $E.f$ over $t'$, composing $g$ with the product $P\cdot Q$ gives the product of $P \circ g$ and $Q \circ g$ over $t'$ followed by $\operatorname{Spec}\varphi$, and such that $g$ intertwines the two $\Lambda$-actions. The conclusion asserts the existence of a commutative ring $T_1$ which is local and noetherian, ring maps $\psi : T \to T_1$ and $\varphi_1 : T_1 \to R$ with $\varphi_1 \circ \psi = \varphi$, $\varphi_1$ injective and local, a fake elliptic curve $E_1$ over $T_1$, and morphisms $g_1 : E.A \to E_1.A$ and $h : E_1.A \to E_T.A$, cartesian over $\operatorname{Spec}\varphi_1$ and $\operatorname{Spec}\psi$ respectively, with $g_1$ followed by $h$ equal to $g$, with $g_1$ compatible with the group laws and with the $\Lambda$-actions, and with $h$ compatible with the group laws (no compatibility of $h$ with the $\Lambda$-actions is asserted).
--
--   This is the bookkeeping step that replaces a noetherian base $T$ dominating a local ring $R$ by a local noetherian base, namely the localisation of $T$ at the contraction of the maximal ideal of $R$, while carrying the fake elliptic curve along. It feeds the construction of the canonically polarised local model used in the Čerednik–Drinfeld analysis of quaternionic Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalRing_injective_isLocalHom_isPullback_comp_eq_of_injective
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) {T R : Type} [CommRing T] [CommRing R] [IsNoetherianRing T] [IsLocalRing R]
    (φ : T →+* R) (hφ : Function.Injective φ)
    (ET : FakeEllipticCurve Λ N T) (E : FakeEllipticCurve Λ N R) (g : E.A ⟶ ET.A)
    (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom φ)))
    (hlaw : (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ g =
            (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
              ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1))
    (hact : ∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) :
    ∃ (T₁ : Type) (_ : CommRing T₁) (_ : IsLocalRing T₁) (_ : IsNoetherianRing T₁) (ψ : T →+* T₁) (φ₁ : T₁ →+* R),
      φ₁.comp ψ = φ ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧
      ∃ (E₁ : FakeEllipticCurve Λ N T₁) (g₁ : E.A ⟶ E₁.A)
        (hg₁ : CategoryTheory.IsPullback g₁ E.f E₁.f (Spec.map (CommRingCat.ofHom φ₁)))
        (h : E₁.A ⟶ ET.A) (hh : CategoryTheory.IsPullback h E₁.f ET.f (Spec.map (CommRingCat.ofHom ψ))),
        g₁ ≫ h = g ∧
        (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ g₁ =
            (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ₁))
              ⟨P.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g₁, by rw [Category.assoc, hg₁.w, ← Category.assoc, Q.2]⟩).1) ∧
        (∀ x : ↥Λ, E.act x ≫ g₁ = g₁ ≫ E₁.act x) ∧
        (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of T₁)) (P Q : SchemeHomOver t' E₁.f),
          (E₁.L.mul t' P Q).1 ≫ h =
            (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψ))
              ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) := by sorry
