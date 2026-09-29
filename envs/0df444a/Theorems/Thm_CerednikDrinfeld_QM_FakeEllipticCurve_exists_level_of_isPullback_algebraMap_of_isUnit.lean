-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_level_of_isPullback_algebraMap_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/a44dccfb-1d94-50ee-953c-5bc5a8fe959f
-- title:
--   Extending a fake elliptic curve's level-N structure over a DVR
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$, a discrete valuation domain $R$ with fraction field $K$, and assume the image of $N$ in $R$ is a unit. Let $E_0$ be a `FakeEllipticCurve` for $(\Lambda,N)$ over $K$, so in particular $E_0$ carries a scheme $E_0.A$ over $\operatorname{Spec} K$ with a commutative relative group law $E_0.L$ on its functor of points, an abelian-scheme property bundle (smooth, proper, connected fibres, group law present), a $\Lambda$-action $E_0.\mathrm{act}$ over the base and a level structure $E_0.\mathrm{lev}$. Let $f : \mathcal A \to \operatorname{Spec} R$ come with a relative group law $L$ that is commutative, and with an abelian-scheme property bundle; let $g : E_0.A \to \mathcal A$ exhibit $E_0.f$ as the base change of $f$ along $\operatorname{Spec} K \to \operatorname{Spec} R$ (a pullback square), and assume $g$ transports the multiplication of $E_0.L$ on $T$-points over $\operatorname{Spec} K$ to that of $L$ on the composed $T$-points over $\operatorname{Spec} R$. Finally let $\mathrm{act} : \Lambda \to (\mathcal A \to \mathcal A)$ consist of endomorphisms over $\operatorname{Spec} R$ with $E_0.\mathrm{act}(x)$ followed by $g$ equal to $g$ followed by $\mathrm{act}(x)$ for all $x \in \Lambda$. Then there exist a scheme $C$ and a morphism $\mathrm{lev} : C \to \mathcal A$ such that: $\mathrm{lev}$ is a closed immersion; for all $T$-points $P,Q$ of $f$ factoring through $\mathrm{lev}$ (i.e. $P$ is $P_0$ followed by $\mathrm{lev}$ for some $P_0 : T \to C$), both $L.\mathrm{mul}\,P\,Q$ and $L.\mathrm{inv}\,P$ factor through $\mathrm{lev}$; the unit section $L.\mathrm{one}$ always factors through $\mathrm{lev}$; every $T$-point factoring through $\mathrm{lev}$ is killed by $N$, i.e. its $N$-fold iterated sum $\mathrm{nsmulPt}\,L\,t\,N\,P$ equals $L.\mathrm{one}\,t$; the set of points factoring through $\mathrm{lev}$ is stable under pushing forward by each $\mathrm{act}(x)$, $x \in \Lambda$; the composite $\mathrm{lev}$ followed by $f$ is finite, flat and locally of finite presentation, with fibre rank $N^2$ at every point of $\operatorname{Spec} R$; for every algebraically closed field $k$ and ring homomorphism $sk : R \to k$ with $N \ne 0$ in $k$ there is a bijection $\mathbb Z/N \times \mathbb Z/N \simeq \{P \text{ a } k\text{-point of } f \text{ over } sk : P \text{ factors through } \mathrm{lev}\}$ carrying addition to $L.\mathrm{mul}$; and every $T$-point $P$ of $E_0.f$ factoring through $E_0.\mathrm{lev}$ has $P$ followed by $g$ factoring through $\mathrm{lev}$.
--
--   This is the level-structure half of the good-reduction extension theorem for fake elliptic curves: given an abelian-scheme model $\mathcal A/R$ of the generic fibre $E_0/K$ together with an extension of the $\Lambda$-action, it produces the finite flat subgroup scheme of rank $N^2$ that serves as a level-$N$ structure on $\mathcal A$ and is compatible with the one on $E_0$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_isPullback), where the resulting data are assembled into a fake elliptic curve over $R$ whose base change to $K$ is $E_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_level_of_isPullback_algebraMap_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_level_of_isPullback_algebraMap_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (hN : IsUnit ((N : ℕ) : R))
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ act x) :
    ∃ (C : Scheme.{u}) (lev : C ⟶ 𝒜),
      IsClosedImmersion lev ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
        FactorsThrough lev P → FactorsThrough lev Q →
          FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
        FactorsThrough lev P → nsmulPt L t N P = L.one t) ∧
      (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
        FactorsThrough lev P → FactorsThrough lev (pushPt (act x) (act_over x) P)) ∧
      IsFinite (lev ≫ f) ∧ Flat (lev ≫ f) ∧ LocallyOfFinitePresentation (lev ≫ f) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), (N : k) ≠ 0 →
        ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
          ∀ x y : ZMod N × ZMod N,
            (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1 ≫ g) := by sorry
