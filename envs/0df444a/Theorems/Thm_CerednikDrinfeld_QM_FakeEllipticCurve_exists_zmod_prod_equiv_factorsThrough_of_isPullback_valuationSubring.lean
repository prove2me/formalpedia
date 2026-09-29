-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ce79c332-739f-596d-9c07-d56f816df526
-- title:
--   Geometric fibres of an ℓ-torsion subgroup scheme are (ℤ/ℓ)²
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a valuation subring $O$ of $\overline{\mathbb{Q}}$ and a natural number $\ell$. Let $\mathcal{A}$ be a fake elliptic curve of type $(\Lambda,N)$ over $O$ and $E$ one over $\overline{\mathbb{Q}}$, and let $gE : E.A \to \mathcal{A}.A$ be a morphism making the square with the structure morphisms $E.f$, $\mathcal{A}.f$ and $\mathrm{Spec}$ of the inclusion $O \hookrightarrow \overline{\mathbb{Q}}$ a pullback, such that for all test schemes $T$ over $\overline{\mathbb{Q}}$ and all $T$-points $P,Q$ of $E$ the composite of $E.L.\mathrm{mul}(P,Q)$ with $gE$ is $\mathcal{A}.L.\mathrm{mul}$ of the two composites. Let $K$ be an extra level structure at $\ell$ on $E$. Let $\iota : Kk \to \mathcal{A}.A$ be a closed immersion whose composite with $\mathcal{A}.f$ is finite, flat and locally of finite presentation, of fibre rank $\ell^2$ at every point of $\mathrm{Spec}\,O$, and assume: for every scheme $T$ over $\mathrm{Spec}\,O$, the $T$-points of $\mathcal{A}$ which factor through $\iota$ are closed under the relative group law $\mathcal{A}.L$ and under inversion, the identity section factors through $\iota$, and any such point is killed by $\ell$ in the sense that its $\ell$-fold iterated sum under $\mathcal{A}.L$ is the identity section; finally, for every $T$-point $P$ of $E$ over $\overline{\mathbb{Q}}$, $P$ factors through $K.\mathrm{levK}$ precisely when $P$ composed with $gE$ factors through $\iota$. The conclusion: for every algebraically closed field $k$ and every ring homomorphism $sk : O \to k$ with $\ell \neq 0$ in $k$, there is a bijection $e$ from $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ onto the set of sections $\mathrm{Spec}\,k \to \mathcal{A}.A$ over $\mathrm{Spec}(sk)$ that factor through $\iota$, which carries addition to the relative group law $\mathcal{A}.L$ over that base point.
--
--   This is the fibre-constancy statement for a finite flat subgroup scheme of order $\ell^2$ killed by $\ell$: over a geometric point of the base in which $\ell$ is invertible the subgroup is étale, hence constant, and its group of points is $(\mathbb{Z}/\ell)^2$. It supplies the `levK_fibre` clause needed by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_ker_of_isPullback_valuationSubring_of_comp_eq_act_of_one_mem), which assembles an extra level structure at $\ell$ on a fake elliptic curve over the valuation ring $O$ from the kernel data over the algebraic closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    (𝒜 : FakeEllipticCurve Λ N ↥O) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (K : E.ExtraLevel ℓ)
    {Kk : Scheme.{0}} (ι : Kk ⟶ 𝒜.A) [IsClosedImmersion ι]
    [IsFinite (ι ≫ 𝒜.f)] [Flat (ι ≫ 𝒜.f)] [LocallyOfFinitePresentation (ι ≫ 𝒜.f)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of ↥O)), (ι ≫ 𝒜.f).finrank s = ℓ ^ 2)
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → FactorsThrough ι Q →
        FactorsThrough ι (𝒜.L.mul t P Q) ∧ FactorsThrough ι (𝒜.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)), FactorsThrough ι (𝒜.L.one t))
    (htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P : SchemeHomOver t 𝒜.f),
      FactorsThrough ι P → nsmulPt 𝒜.L t ℓ P = 𝒜.L.one t)
    (hgen : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t' E.f),
      FactorsThrough K.levK P ↔ ∃ P₀ : T ⟶ Kk, P₀ ≫ ι = P.1 ≫ gE) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥O →+* k), (ℓ : k) ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) 𝒜.f // FactorsThrough ι P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) 𝒜.f) =
          𝒜.L.mul (geomPoint k sk) (e x) (e y) := by sorry
