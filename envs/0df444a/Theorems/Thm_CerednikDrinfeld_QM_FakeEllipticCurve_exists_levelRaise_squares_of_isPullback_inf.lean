-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelRaise_squares_of_isPullback_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c0d78789-bf7f-5279-9211-5f06ce73f574
-- title:
--   Enlarging the base field in a fake elliptic curve square
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q,a,b]$ and $N \in \mathbb N$. Let $O$ be a valuation subring of $\overline{\mathbb Q}$ and $K' , K''$ intermediate fields of $\overline{\mathbb Q}/\mathbb Q$, and let $j : K' \to K''$, $\iota_0 : O \cap K' \to O$, $j_0 : O \cap K' \to K'$, $\iota_1 : O \cap K'' \to O$, $j_1 : O \cap K'' \to K''$ be ring maps each compatible with the given inclusions into $\overline{\mathbb Q}$. Let $\mathcal A_0, \mathcal A, E, E_0$ be objects of type `FakeEllipticCurve Λ N` over $O \cap K'$, $O$, $\overline{\mathbb Q}$, $K'$ respectively, i.e. schemes with a commutative relative group law, the abelian‑scheme property bundle, two‑dimensional fibres and a $\Lambda$‑action, together with level data. Assume given $p : \mathcal A.A \to \mathcal A_0.A$ making a cartesian square over $\mathrm{Spec}(\iota_0)$, and $g_0 : E_0.A \to \mathcal A_0.A$, $g_E : E.A \to \mathcal A.A$, $g_E' : E.A \to E_0.A$ cartesian over $\mathrm{Spec}(j_0)$, $\mathrm{Spec}(O \hookrightarrow \overline{\mathbb Q})$, $\mathrm{Spec}(K' \hookrightarrow \overline{\mathbb Q})$ respectively, each carrying $T$‑point multiplications to multiplications of images and commuting with every $\Lambda$‑action, and assume $p \circ g_E = g_0 \circ g_E'$. Then there exist fake elliptic curves $\mathcal A_1$ over $O \cap K''$ and $E_2$ over $K''$, a morphism $p_1 : \mathcal A.A \to \mathcal A_1.A$ cartesian over $\mathrm{Spec}(\iota_1)$, and morphisms $r_E : E.A \to E_2.A$, $g_{E_2} : E_2.A \to \mathcal A_1.A$, $q_E : E_2.A \to E_0.A$, cartesian over $\mathrm{Spec}(K'' \hookrightarrow \overline{\mathbb Q})$, $\mathrm{Spec}(j_1)$, $\mathrm{Spec}(j)$ and compatible with the group laws and the $\Lambda$‑actions in the same sense, such that $q_E \circ r_E = g_E'$ and $p_1 \circ g_E = g_{E_2} \circ r_E$.
--
--   This is the base‑change bookkeeping step that replaces the pair $(O \cap K', K')$ by $(O \cap K'', K'')$ for a quaternionic (fake elliptic) abelian surface model, producing all four comparison squares of the resulting cube at once; note that the comparison morphisms are required to satisfy the cartesian, group‑law and $\Lambda$‑equivariance conditions, but not the level‑structure clause. It is used in the extension of homomorphisms over a valuation subring, `exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`, so that a single base ring serves two models simultaneously.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelRaise_squares_of_isPullback_inf
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (K' K'' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (j : ↥K' →+* ↥K'') (hj : ∀ x : ↥K', ((j x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O) (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥K') (hj₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (ι₁ : ↥(O.toSubring ⊓ K''.toSubring) →+* ↥O) (hι₁ : ∀ x : ↥(O.toSubring ⊓ K''.toSubring), (ι₁ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₁ : ↥(O.toSubring ⊓ K''.toSubring) →+* ↥K'') (hj₁ : ∀ x : ↥(O.toSubring ⊓ K''.toSubring), ((j₁ x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring)) (𝒜 : FakeEllipticCurve Λ N ↥O)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (E₀ : FakeEllipticCurve Λ N ↥K')
    (p : 𝒜.A ⟶ 𝒜₀.A) (hp : CategoryTheory.IsPullback p 𝒜.f 𝒜₀.f (Spec.map (CommRingCat.ofHom ι₀)))
    (g₀ : E₀.A ⟶ 𝒜₀.A) (hg₀ : CategoryTheory.IsPullback g₀ E₀.f 𝒜₀.f (Spec.map (CommRingCat.ofHom j₀)))
    (hg₀_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g₀ =
        (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₀))
          ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1)
    (hg₀_act : ∀ x : ↥Λ, E₀.act x ≫ g₀ = g₀ ≫ 𝒜₀.act x)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gE' : E.A ⟶ E₀.A) (hgE' : CategoryTheory.IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgE'_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE' =
        (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, Q.2]⟩).1)
    (hgE'_act : ∀ x : ↥Λ, E.act x ≫ gE' = gE' ≫ E₀.act x)
    (hcube : gE ≫ p = gE' ≫ g₀) :
    ∃ (𝒜₁ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K''.toSubring)) (E₂ : FakeEllipticCurve Λ N ↥K'')
      (p₁ : 𝒜.A ⟶ 𝒜₁.A) (hp₁ : CategoryTheory.IsPullback p₁ 𝒜.f 𝒜₁.f (Spec.map (CommRingCat.ofHom ι₁)))
      (rE : E.A ⟶ E₂.A) (hrE : CategoryTheory.IsPullback rE E.f E₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
      (hrE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ rE =
        (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, Q.2]⟩).1)
      (hrE_act : ∀ x : ↥Λ, E.act x ≫ rE = rE ≫ E₂.act x)
      (gE₂ : E₂.A ⟶ 𝒜₁.A) (hgE₂ : CategoryTheory.IsPullback gE₂ E₂.f 𝒜₁.f (Spec.map (CommRingCat.ofHom j₁)))
      (hgE₂_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ gE₂ =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₁))
          ⟨P.1 ≫ gE₂, by rw [Category.assoc, hgE₂.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE₂, by rw [Category.assoc, hgE₂.w, ← Category.assoc, Q.2]⟩).1)
      (hgE₂_act : ∀ x : ↥Λ, E₂.act x ≫ gE₂ = gE₂ ≫ 𝒜₁.act x)
      (qE : E₂.A ⟶ E₀.A) (hqE : CategoryTheory.IsPullback qE E₂.f E₀.f (Spec.map (CommRingCat.ofHom j)))
      (hqE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ qE =
        (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j))
          ⟨P.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, Q.2]⟩).1)
      (hqE_act : ∀ x : ↥Λ, E₂.act x ≫ qE = qE ≫ E₀.act x)
      , rE ≫ qE = gE' ∧ gE ≫ p₁ = rE ≫ gE₂ := by sorry
