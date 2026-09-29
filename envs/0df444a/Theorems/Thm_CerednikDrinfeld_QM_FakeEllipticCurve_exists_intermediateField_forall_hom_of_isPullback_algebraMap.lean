-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_hom_of_isPullback_algebraMap
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_hom_of_isPullback_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d170999c-5f23-5893-98b1-6109400711eb
-- title:
--   Descent of a homomorphism of fake elliptic curves to a finite extension
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, and an intermediate field $K'$ of $\mathbb Q \subseteq \overline{\mathbb Q}$ that is finite-dimensional over $\mathbb Q$. Let $\mathcal A_1,\mathcal D_1$ be objects of `FakeEllipticCurve Λ N K'` and $E,d$ objects of `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)`; each such object consists of a scheme with a structure morphism to the spectrum of the base ring, a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, and a $\Lambda$-action with the stated compatibilities. Assume given $g_E : E.A \to \mathcal A_1.A$ making the square with $E.f$, $\mathcal A_1.f$ and $\operatorname{Spec}$ of the inclusion $K' \hookrightarrow \overline{\mathbb Q}$ cartesian, such that for every scheme $T$, every $t' : T \to \operatorname{Spec}\overline{\mathbb Q}$ and all $T$-points $P,Q$ of $E$ over $t'$, composing the product $P\cdot Q$ with $g_E$ equals the product in $\mathcal A_1$ of $P \cdot g_E$ and $Q \cdot g_E$ over $t'$ followed by $\operatorname{Spec}$ of the inclusion, and such that $g_E$ intertwines the $\Lambda$-actions ($E.\mathrm{act}\,x$ followed by $g_E$ equals $g_E$ followed by $\mathcal A_1.\mathrm{act}\,x$ for all $x \in \Lambda$); assume the same data $g_d$ for $d$ and $\mathcal D_1$. Let $\varphi : E.A \to d.A$ satisfy $\varphi$ followed by $d.f$ equals $E.f$, carry products to products in the sense that `mapPt φ hφ` commutes with the group laws on all $T$-points, and commute with the $\Lambda$-actions. The conclusion asserts the existence of an intermediate field $K_\varphi$ of $\mathbb Q \subseteq \overline{\mathbb Q}$, finite-dimensional over $\mathbb Q$ and containing $K'$, with the following universal property: for every intermediate field $K'' \supseteq K_\varphi$, every ring homomorphism $j : K' \to K''$ compatible with the inclusions into $\overline{\mathbb Q}$, all $\mathcal A_2,\mathcal D_2$ in `FakeEllipticCurve Λ N K''`, and all morphisms $r_E : E.A \to \mathcal A_2.A$, $q_E : \mathcal A_2.A \to \mathcal A_1.A$, $r_d : d.A \to \mathcal D_2.A$, $q_d : \mathcal D_2.A \to \mathcal D_1.A$ whose squares over $\operatorname{Spec}\overline{\mathbb Q} \to \operatorname{Spec} K''$ and $\operatorname{Spec} j$ are cartesian, which satisfy the corresponding compatibilities with the group laws and the $\Lambda$-actions and which factor the given data ($r_E$ followed by $q_E$ equals $g_E$, and $r_d$ followed by $q_d$ equals $g_d$), there is a morphism $\varphi_2 : \mathcal A_2.A \to \mathcal D_2.A$ with $\varphi_2$ followed by $\mathcal D_2.f$ equal to $\mathcal A_2.f$, with $r_E$ followed by $\varphi_2$ equal to $\varphi$ followed by $r_d$, compatible with the group laws on all $T$-points over $\operatorname{Spec} K''$, and commuting with the $\Lambda$-actions. The base-change data are spelled out as explicit cartesian squares together with the group-law and $\Lambda$-action compatibilities; the clause of the project predicate `CerednikDrinfeld.QM.IsPullback` concerning factorisation through the level structure `lev` is neither assumed nor produced.
--
--   This is the descent statement that a homomorphism between the geometric generic fibres of two fake elliptic curves over a number field is already defined over a finite extension, in a form universal in the intermediate model: the field $K_\varphi$ is chosen once and serves every larger $K''$ and every choice of $K''$-models refining the given ones. It is used in the Čerednik–Drinfel'd part of the development to extend homomorphisms over a valuation subring, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_hom_of_isPullback_algebraMap.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_hom_of_isPullback_algebraMap
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K']
    (𝒜₁ 𝒟₁ : FakeEllipticCurve Λ N ↥K') (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜₁.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜₁.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜₁.act x)
    (gd : d.A ⟶ 𝒟₁.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟₁.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟₁.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Kφ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥Kφ) (_ : K' ≤ Kφ),
      ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : Kφ ≤ K'')
        (j : ↥K' →+* ↥K'') (_ : ∀ x : ↥K', ((j x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
        (𝒜₂ 𝒟₂ : FakeEllipticCurve Λ N ↥K'')
        (rE : E.A ⟶ 𝒜₂.A) (hrE : CategoryTheory.IsPullback rE E.f 𝒜₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
    (hrE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ rE =
        (𝒜₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, Q.2]⟩).1)
    (hrE_act : ∀ x : ↥Λ, E.act x ≫ rE = rE ≫ 𝒜₂.act x)
        (qE : 𝒜₂.A ⟶ 𝒜₁.A) (hqE : CategoryTheory.IsPullback qE 𝒜₂.f 𝒜₁.f (Spec.map (CommRingCat.ofHom (j))))
    (hqE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' 𝒜₂.f),
      (𝒜₂.L.mul t' P Q).1 ≫ qE =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (j)))
          ⟨P.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, Q.2]⟩).1)
    (hqE_act : ∀ x : ↥Λ, 𝒜₂.act x ≫ qE = qE ≫ 𝒜₁.act x)
        (_ : rE ≫ qE = gE)
        (rd : d.A ⟶ 𝒟₂.A) (hrd : CategoryTheory.IsPullback rd d.f 𝒟₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
    (hrd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ rd =
        (𝒟₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rd, by rw [Category.assoc, hrd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rd, by rw [Category.assoc, hrd.w, ← Category.assoc, Q.2]⟩).1)
    (hrd_act : ∀ x : ↥Λ, d.act x ≫ rd = rd ≫ 𝒟₂.act x)
        (qd : 𝒟₂.A ⟶ 𝒟₁.A) (hqd : CategoryTheory.IsPullback qd 𝒟₂.f 𝒟₁.f (Spec.map (CommRingCat.ofHom (j))))
    (hqd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' 𝒟₂.f),
      (𝒟₂.L.mul t' P Q).1 ≫ qd =
        (𝒟₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (j)))
          ⟨P.1 ≫ qd, by rw [Category.assoc, hqd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qd, by rw [Category.assoc, hqd.w, ← Category.assoc, Q.2]⟩).1)
    (hqd_act : ∀ x : ↥Λ, 𝒟₂.act x ≫ qd = qd ≫ 𝒟₁.act x)
        (_ : rd ≫ qd = gd),
        ∃ (φ₂ : 𝒜₂.A ⟶ 𝒟₂.A) (hφ₂ : φ₂ ≫ 𝒟₂.f = 𝒜₂.f),
          rE ≫ φ₂ = φ ≫ rd ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t 𝒜₂.f),
            mapPt φ₂ hφ₂ (𝒜₂.L.mul t P Q) = 𝒟₂.L.mul t (mapPt φ₂ hφ₂ P) (mapPt φ₂ hφ₂ Q)) ∧
          (∀ x : ↥Λ, 𝒜₂.act x ≫ φ₂ = φ₂ ≫ 𝒟₂.act x) := by sorry
