-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/812caed0-00e2-5510-b74b-6c4ec53b7554
-- title:
--   Extending homomorphisms of fake elliptic curves over a DVR
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and $N \in \mathbb{N}$. Let $R$ be a discrete valuation domain with fraction field $K$, let $\mathcal{A},\mathcal{D}$ be objects of `FakeEllipticCurve Λ N R` and $E,d$ objects of `FakeEllipticCurve Λ N K` — that is, schemes $\mathcal{A}.A$, etc., with structure morphisms to $\mathrm{Spec}$ of the base, a commutative relative group law on scheme-valued points, the property bundle (smooth, proper, connected fibres, group law present), two-dimensional fibres, a $\Lambda$-action by base-preserving endomorphisms satisfying the multiplicativity, additivity and trace axioms, together with the level data. Assume given $g_E : E.A \to \mathcal{A}.A$ and $g_d : d.A \to \mathcal{D}.A$ each making a cartesian square with the structure morphisms over $\mathrm{Spec}\,K \to \mathrm{Spec}\,R$, each carrying the group law on $K$-scheme-valued points to the group law on the base-changed points, and each $\Lambda$-equivariant ($E.\mathrm{act}\,x$ followed by $g_E$ equals $g_E$ followed by $\mathcal{A}.\mathrm{act}\,x$, likewise for $g_d$); these are the first three clauses of the project's `IsPullback` relation, the clause on factorisation through the level scheme not being assumed. Assume further $\varphi : E.A \to d.A$ over $\mathrm{Spec}\,K$ which is a homomorphism on $T$-points for every $K$-scheme $T$ and satisfies $\varphi \circ E.\mathrm{act}\,x = d.\mathrm{act}\,x \circ \varphi$ in diagrammatic form. Then there is $\Phi : \mathcal{A}.A \to \mathcal{D}.A$ over $\mathrm{Spec}\,R$ with $\Phi \circ g_E = g_d \circ \varphi$, which is a homomorphism on $T$-points for every $R$-scheme $T$ and commutes with the $\Lambda$-actions.
--
--   This is the weak Néron mapping property for abelian schemes in the setting of fake elliptic curves: a $\Lambda$-equivariant homomorphism between the generic fibres extends uniquely to a $\Lambda$-equivariant homomorphism of the integral models over the discrete valuation ring. It is the discretely valued case used to obtain the corresponding extension statement over a general valuation ring, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (𝒜 𝒟 : FakeEllipticCurve Λ N R) (E d : FakeEllipticCurve Λ N K)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f),
      gE ≫ Φ = φ ≫ gd ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by sorry
