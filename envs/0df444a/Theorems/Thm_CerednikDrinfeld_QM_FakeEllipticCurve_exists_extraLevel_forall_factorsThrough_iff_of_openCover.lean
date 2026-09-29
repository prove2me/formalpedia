-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/f1593c82-4a62-52a4-b7ac-d5decf4bf010
-- title:
--   Zariski gluing of extra level structures on a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, a fake elliptic curve $E$ of type $(\Lambda,N)$ over $S$ (an abelian scheme $E.f : E.A \to \operatorname{Spec} S$ of relative dimension $2$ with commutative relative group law $E.L$, a $\Lambda$-action $E.act$ and a level structure $E.lev : E.C \to E.A$), and a natural number $n$. Given rings $S_i$ ($i \in \iota$) and homomorphisms $\varphi_i : S \to S_i$ such that each $\operatorname{Spec}\varphi_i$ is an open immersion and these jointly cover $\operatorname{Spec} S$ on points, fake elliptic curves $E_i$ of type $(\Lambda,N)$ over $S_i$, and morphisms $g_i : (E_i).A \to E.A$ making each square over $\operatorname{Spec}\varphi_i$ cartesian, compatible with the group laws on $T$-points, $\Lambda$-equivariant, and such that a point of $E_i$ whose image factors through $E.lev$ already factors through $(E_i).lev$. Suppose for each $i$ an extra level structure $K_i$ of order $n$ on $E_i$ is given (a closed subscheme of $(E_i).A$, finite flat of fibre rank $n^2$, stable under the group law, the inverse and $\Lambda$, killed by $n$, meeting the level structure only in the identity, with geometric fibres $(\mathbb{Z}/n)^2$), and that these agree on overlaps: whenever two points $P_i$, $P_j$ of $E_i$, $E_j$ over a common $T$ have $P_i \circ$-composed with $g_i$ equal to $P_j$ composed with $g_j$, $P_i$ lies in $K_i$ iff $P_j$ lies in $K_j$. Then there is an extra level structure $K_0$ of order $n$ on $E$ whose points are exactly these, i.e. for every $i$ and every point $P$ of $E_i$ over $t$, the image of $P$ under $g_i$ factors through $K_0.levK$ iff $P$ factors through $(K_i).levK$; moreover $K_0$ is unique on points: any $K_1$ with the same property has the same $T$-points as $K_0$ for every test scheme $T$.
--
--   This is the Zariski descent (sheaf) property for the relative moduli problem of extra level structures of order $n$ on a fixed fake elliptic curve: such structures, given over an open cover of the base together with agreement on overlaps, glue uniquely. It is the gluing input for the representability of the fine moduli problem for fake elliptic curves with an added $\Gamma_0$-type datum, and is used in the construction of the finite étale fine moduli schemes in that setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (n : ℕ)
    {ι : Type u} (Sᵢ : ι → Type u) [∀ i, CommRing (Sᵢ i)] (φ : ∀ i, S →+* Sᵢ i)
    (hopen : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ i))))
    (hcover : ∀ x : ↥(Spec (CommRingCat.of S)), ∃ i, x ∈ Set.range (Spec.map (CommRingCat.ofHom (φ i))).base)
    (Eᵢ : ∀ i, FakeEllipticCurve Λ N (Sᵢ i))
    (g : ∀ i, (Eᵢ i).A ⟶ E.A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (Eᵢ i).f E.f (Spec.map (CommRingCat.ofHom (φ i))))
    (hg_mul : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P Q : SchemeHomOver t (Eᵢ i).f),
      ((Eᵢ i).L.mul t P Q).1 ≫ g i =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ (i : ι) (x : ↥Λ), (Eᵢ i).act x ≫ g i = g i ≫ E.act x)
    (hg_lev : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
      FactorsThrough E.lev (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ →
        FactorsThrough (Eᵢ i).lev P)
    (K : ∀ i, (Eᵢ i).ExtraLevel n)
    (hK : ∀ (i j : ι) {T : Scheme.{u}}
      (tᵢ : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (tⱼ : T ⟶ Spec (CommRingCat.of (Sᵢ j)))
      (Pᵢ : SchemeHomOver tᵢ (Eᵢ i).f) (Pⱼ : SchemeHomOver tⱼ (Eᵢ j).f),
      Pᵢ.1 ≫ g i = Pⱼ.1 ≫ g j → (FactorsThrough (K i).levK Pᵢ ↔ FactorsThrough (K j).levK Pⱼ)) :
    ∃ K₀ : E.ExtraLevel n,
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
        FactorsThrough K₀.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
            ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
          FactorsThrough (K i).levK P) ∧
      (∀ K₁ : E.ExtraLevel n,
        (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
          FactorsThrough K₁.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
              ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
            FactorsThrough (K i).levK P) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K₁.levK P ↔ FactorsThrough K₀.levK P) := by sorry
