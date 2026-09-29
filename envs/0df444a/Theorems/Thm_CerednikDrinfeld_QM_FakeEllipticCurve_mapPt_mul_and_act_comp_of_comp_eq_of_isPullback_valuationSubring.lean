-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/dd914b99-7204-5ee0-ac92-feb5a3069a5d
-- title:
--   Extensions over a valuation ring are automatically homomorphisms
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a valuation subring $O$ of $\overline{\mathbb{Q}}$. Let $\mathcal{A},\mathcal{D}$ be objects of `FakeEllipticCurve Λ N ↥O` and $E,d$ objects of `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)`; each such object consists of a scheme with a structure morphism to the spectrum of its base, a commutative relative group law on its functor of sections, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base, and further level data. Assume given $g_E : E.A \to \mathcal{A}.A$ forming a pullback square of $E.f$ along $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$, compatible with the two group laws (the product of two sections, composed with $g_E$, is the product of their composites with $g_E$, taken over the base change of the test morphism) and with the $\Lambda$-actions, i.e. $E.\mathrm{act}\,x$ followed by $g_E$ equals $g_E$ followed by $\mathcal{A}.\mathrm{act}\,x$ for all $x \in \Lambda$; likewise $g_d$ for $d$ and $\mathcal{D}$. Assume $\varphi : E.A \to d.A$ is a morphism over $\overline{\mathbb{Q}}$ ($\varphi$ followed by $d.f$ is $E.f$) which respects the group laws, in the sense that composing sections with $\varphi$ (the operation `mapPt`) carries products to products, and satisfies $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $d.\mathrm{act}\,x$. Finally let $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ be any morphism over $\operatorname{Spec} O$ with $g_E$ followed by $\Phi$ equal to $\varphi$ followed by $g_d$. The conclusion is that $\Phi$ respects the group laws, i.e. for every scheme $T$, every $t : T \to \operatorname{Spec} O$ and all sections $P,Q$ of $\mathcal{A}.f$ over $t$, composing with $\Phi$ sends the product of $P$ and $Q$ to the product of their composites, and that $\mathcal{A}.\mathrm{act}\,x$ followed by $\Phi$ equals $\Phi$ followed by $\mathcal{D}.\mathrm{act}\,x$ for every $x \in \Lambda$.
--
--   This is the rigidity (density) half of the statement that a homomorphism between the generic fibres of two fake elliptic curves over a valuation subring of $\overline{\mathbb{Q}}$ extends to a homomorphism of the integral models: any extension as a morphism of $O$-schemes is automatically compatible with the relative group laws and with the quaternionic $\Lambda$-action. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf), and rests on the comparison principle [`AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated`](thm.html#AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated) for morphisms out of a smooth scheme into a separated one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
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
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x)
    (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f) (hext : gE ≫ Φ = φ ≫ gd) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by sorry
