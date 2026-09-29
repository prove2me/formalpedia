-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
-- name    : CerednikDrinfeld.QM.exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/919ec1f7-5834-5f68-825c-4cf2c0cf4dcf
-- title:
--   Invertible-level subgroup of the generic fibre extends étale
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, with fraction field $K$. Let $f\colon\mathcal A\to\operatorname{Spec} R$ carry a relative group law $L$ (functorial group structures on the sets $\mathcal A(T)$ of morphisms over $\operatorname{Spec} R$, natural in $T$) which is commutative, and satisfy `AbelianSchemePropertyBundle`: $f$ is smooth and proper, its fibres are connected, and it admits a relative group law. Let $fP\colon P\to\operatorname{Spec} K$ carry a commutative relative group law $L_P$ and satisfy the same bundle of properties, and let $g\colon P\to\mathcal A$ exhibit the square with $fP$, $f$ and $\operatorname{Spec}(K)\to\operatorname{Spec}(R)$ as a pullback, compatibly with multiplication on points: for every $K$-scheme $T$ and points $x,y$ of $P$ over $t'$, composing $L_P$-product with $g$ gives the $L$-product of $x\circ g$ and $y\circ g$. Let $(\mathrm{act}_i)_{i\in\iota}$ be endomorphisms of $P$ over $K$ and $(\mathrm{act}'_i)$ endomorphisms of $\mathcal A$ over $R$ with $\mathrm{act}_i$ followed by $g$ equal to $g$ followed by $\mathrm{act}'_i$. Let $N\in\mathbb N$ with $N$ a unit in $R$, and let $\mathrm{lev}_0\colon C_0\to P$ be a closed immersion such that, for every $K$-scheme $T$, the points of $P$ over $T$ factoring through $\mathrm{lev}_0$ are closed under $L_P$-product and $L_P$-inverse, contain the unit, are killed by $N$ (the $N$-fold $L_P$-sum is the unit), and are stable under each $\mathrm{act}_i$; moreover $\mathrm{lev}_0$ followed by $fP$ is finite and flat of fibrewise rank $N^2$ at every point of $\operatorname{Spec} K$. Then there exist a scheme $C$ and a closed immersion $\mathrm{lev}\colon C\to\mathcal A$ such that, for every $R$-scheme $T$, the points of $\mathcal A$ over $T$ factoring through $\mathrm{lev}$ are closed under $L$-product and $L$-inverse, contain the unit, are killed by $N$, and are stable under each $\mathrm{act}'_i$; the composite $\mathrm{lev}$ followed by $f$ is finite, flat, locally of finite presentation and étale, with fibrewise rank $N^2$ at every point of $\operatorname{Spec} R$; and for every $K$-scheme $T$ a point $x$ of $P$ over $t'$ factors through $\mathrm{lev}_0$ if and only if $x$ followed by $g$ factors through $\mathrm{lev}$.
--
--   This is the step asserting that a level structure on the generic fibre extends to the smooth proper model when the level $N$ is invertible in the base, the extension being the unique finite flat étale closed subgroup scheme of rank $N^2$ with the prescribed generic fibre. It is used in constructing a fake elliptic curve with level structure over the discrete valuation ring from one over its fraction field, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit) and [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_isClosedImmersion_etale_factorsThrough_iff_of_isPullback_of_isUnit
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP) (hcP : LP.IsCommutative)
    (hP : AbelianSchemePropertyBundle K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    {ι : Type v} (act : ι → (P ⟶ P)) (act_over : ∀ i : ι, act i ≫ fP = fP)
    (act' : ι → (𝒜 ⟶ 𝒜)) (act'_over : ∀ i : ι, act' i ≫ f = f)
    (hact : ∀ i : ι, act i ≫ g = g ≫ act' i)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C₀ : Scheme.{u}} (lev₀ : C₀ ⟶ P) (lev₀_closed : IsClosedImmersion lev₀)
    (lev₀_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ y →
        FactorsThrough lev₀ (LP.mul t x y) ∧ FactorsThrough lev₀ (LP.inv t x))
    (lev₀_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)), FactorsThrough lev₀ (LP.one t))
    (lev₀_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → nsmulPt LP t N x = LP.one t)
    (lev₀_stable : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fP),
      FactorsThrough lev₀ x → FactorsThrough lev₀ (pushPt (act i) (act_over i) x))
    (lev₀_finite : IsFinite (lev₀ ≫ fP)) (lev₀_flat : Flat (lev₀ ≫ fP))
    (lev₀_rank : ∀ s : ↥(Spec (CommRingCat.of K)), (lev₀ ≫ fP).finrank s = N ^ 2) :
    ∃ (C : Scheme.{u}) (lev : C ⟶ 𝒜), IsClosedImmersion lev ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev y →
          FactorsThrough lev (L.mul t x y) ∧ FactorsThrough lev (L.inv t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → nsmulPt L t N x = L.one t) ∧
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        FactorsThrough lev x → FactorsThrough lev (pushPt (act' i) (act'_over i) x)) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧ Etale (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t' fP),
        FactorsThrough lev₀ x ↔ ∃ x₀ : T ⟶ C, x₀ ≫ lev = x.1 ≫ g) := by sorry
