-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d4539339-980e-5d6b-a573-3bc407fa27f9
-- title:
--   Homomorphisms of fake elliptic curves extend over O
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a valuation subring $O$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $\mathcal{A},\mathcal{D}$ be `FakeEllipticCurve Λ N ↥O` and $E,d$ be `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)`, i.e. schemes over the respective base equipped with a commutative relative group law on scheme-valued points, smooth proper structure morphism with connected fibres of Krull dimension $2$, an action of $\Lambda$ by base-preserving endomorphisms additive and multiplicative in $\Lambda$ and additive on points, the trace condition on tangent spaces, and a level-$N$ datum. Assume given a finite intermediate field $K'$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, a ring map $\iota_0 : O \cap K' \to O$ compatible with the inclusions into $\overline{\mathbb{Q}}$, and fake elliptic curves $\mathcal{A}_0,\mathcal{D}_0$ over $O \cap K'$ with `FakeEllipticCurve.IsPullback ι₀` to $\mathcal{A}$ and $\mathcal{D}$: that is, morphisms $\mathcal{A}.A \to \mathcal{A}_0.A$, resp. $\mathcal{D}.A \to \mathcal{D}_0.A$, forming cartesian squares over $\operatorname{Spec}\iota_0$, compatible with the group laws on points and with the $\Lambda$-actions, and carrying points factoring through the level datum of the upper curve to points factoring through that of the lower one. Assume further $g_E : E.A \to \mathcal{A}.A$ and $g_d : d.A \to \mathcal{D}.A$ make cartesian squares exhibiting $E$ and $d$ as the base changes of $\mathcal{A}$ and $\mathcal{D}$ along $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} O$, each compatible with the group laws on points and $\Lambda$-equivariant, and let $\varphi : E.A \to d.A$ be a morphism over $\operatorname{Spec}\overline{\mathbb{Q}}$ which is a homomorphism for the group laws on all $\overline{\mathbb{Q}}$-scheme-valued points and satisfies $E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $d.\mathrm{act}(x)$ for all $x \in \Lambda$. Then there is a morphism $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ over $\operatorname{Spec} O$ with $g_E$ followed by $\Phi$ equal to $\varphi$ followed by $g_d$, such that composition with $\Phi$ turns the group law of $\mathcal{A}$ into that of $\mathcal{D}$ on all $O$-scheme-valued points, and $\mathcal{A}.\mathrm{act}(x)$ followed by $\Phi$ equals $\Phi$ followed by $\mathcal{D}.\mathrm{act}(x)$ for every $x \in \Lambda$.
--
--   This is the Néron mapping property for homomorphisms of abelian schemes with quaternionic multiplication, in the form needed over the (possibly non-noetherian, rank-one) valuation ring $O \subset \overline{\mathbb{Q}}$: a $\Lambda$-equivariant homomorphism between the generic fibres extends over $O$, the extension being obtained from the descent of both models to the discrete valuation ring $O \cap K'$. It is used in the construction of extra level structures and level isogenies for fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))

    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K']
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O) (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ 𝒟₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring))
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜) (h𝒟₀ : FakeEllipticCurve.IsPullback ι₀ 𝒟₀ 𝒟)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f),
      gE ≫ Φ = φ ≫ gd ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by sorry
