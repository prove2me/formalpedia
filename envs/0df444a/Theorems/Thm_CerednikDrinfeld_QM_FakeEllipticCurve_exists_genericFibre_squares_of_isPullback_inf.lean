-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/2b25ea02-0af7-5b40-912e-8a15f5c22d25
-- title:
--   Generic-fibre squares for a fake elliptic curve over O∩ K'
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; throughout, a fake elliptic curve over a commutative ring $S$ means the project's structure `FakeEllipticCurve`: a scheme $A$ over $\operatorname{Spec} S$ carrying a commutative relative group law, smooth and proper with connected fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$ that are additive and multiplicative for the group law and satisfy the trace condition on tangent spaces, plus the level data $C \to A$. Let $O$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and $K'$ an intermediate field $\mathbb{Q} \subseteq K' \subseteq \overline{\mathbb{Q}}$, and let $\iota_0 : O \sqcap K' \to O$ and $j_0 : O \sqcap K' \to K'$ be ring homomorphisms from the intersection of the two underlying subrings, each compatible with the inclusions into $\overline{\mathbb{Q}}$ (hypotheses $h\iota_0$, $hj_0$). Let $\mathcal{A}_0$, $\mathcal{A}$, $E$ be fake elliptic curves for $(\Lambda,N)$ over $O\sqcap K'$, $O$ and $\overline{\mathbb{Q}}$ respectively, with `IsPullback` $\iota_0\,\mathcal{A}_0\,\mathcal{A}$, i.e. some $\mathcal{A}.A \to \mathcal{A}_0.A$ forming a cartesian square over $\operatorname{Spec}\iota_0$ and compatible with the group laws on $T$-points, the $\Lambda$-actions and the level subschemes. Assume further a morphism $g_E : E.A \to \mathcal{A}.A$ making a cartesian square over $\operatorname{Spec}$ of $O \hookrightarrow \overline{\mathbb{Q}}$, compatible with the group laws on $T$-points and with the $\Lambda$-actions. The conclusion produces a fake elliptic curve $E_0$ over $K'$ and morphisms $p : \mathcal{A}.A \to \mathcal{A}_0.A$, $g_0 : E_0.A \to \mathcal{A}_0.A$, $g_E' : E.A \to E_0.A$, cartesian over $\operatorname{Spec}\iota_0$, $\operatorname{Spec} j_0$ and $\operatorname{Spec}$ of $K' \hookrightarrow \overline{\mathbb{Q}}$ respectively, each compatible with the relative group laws on $T$-points and with the $\Lambda$-actions, and such that $g_E$ followed by $p$ equals $g_E'$ followed by $g_0$. The three squares produced are asserted only with group-law and $\Lambda$-action compatibility; no level-structure clause is claimed for them.
--
--   A book-keeping step in the descent of a fake elliptic curve over a valuation subring of $\overline{\mathbb{Q}}$ to a model over a subfield: it fills in the commuting cube whose faces are the base-change squares relating $\mathcal{A}$ over $O$, $\mathcal{A}_0$ over $O\cap K'$, the generic fibre $E$ over $\overline{\mathbb{Q}}$ and a $K'$-model $E_0$. It is used in the extension of morphisms over valuation subrings (`exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O)
    (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (j₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥K')
    (hj₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring)) (𝒜 : FakeEllipticCurve Λ N ↥O)
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x) :
    ∃ (E₀ : FakeEllipticCurve Λ N ↥K')
      (p : 𝒜.A ⟶ 𝒜₀.A) (hp : CategoryTheory.IsPullback p 𝒜.f 𝒜₀.f (Spec.map (CommRingCat.ofHom ι₀)))
      (g₀ : E₀.A ⟶ 𝒜₀.A) (hg₀ : CategoryTheory.IsPullback g₀ E₀.f 𝒜₀.f (Spec.map (CommRingCat.ofHom j₀)))
      (gE' : E.A ⟶ E₀.A)
      (hgE' : CategoryTheory.IsPullback gE' E.f E₀.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t' 𝒜.f),
        (𝒜.L.mul t' P Q).1 ≫ p =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ι₀))
            ⟨P.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ p = p ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (P Q : SchemeHomOver t' E₀.f),
        (E₀.L.mul t' P Q).1 ≫ g₀ =
          (𝒜₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom j₀))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₀.act x ≫ g₀ = g₀ ≫ 𝒜₀.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gE' =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
            ⟨P.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gE', by rw [Category.assoc, hgE'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ gE' = gE' ≫ E₀.act x) ∧
      gE ≫ p = gE' ≫ g₀ := by sorry
