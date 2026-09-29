-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/00b7a70e-e6a6-5cf8-a1d2-445ed411afe8
-- title:
--   Enlarging the finitely generated subalgebra: inverting m and s
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders, natural numbers $N, m$, a commutative ring $L$, a fake elliptic curve $E$ over $L$ of level datum $(\Lambda,N)$, and a full level-$m$ structure $PP$ on $E$. Let $R$ be a finitely generated $\mathbb{Z}$-subalgebra of $L$, let $ER$ be a fake elliptic curve over $R$, and let $g : E.A \to ER.A$ make the square with $E.f$, $ER.f$ and $\operatorname{Spec}(R \hookrightarrow L)$ cartesian; assume $g$ is compatible with the relative group laws on points over arbitrary bases, is $\Lambda$-equivariant, and carries points factoring through $E.\mathrm{lev}$ to points factoring through $ER.\mathrm{lev}$ and conversely. Let $PR$ be a section of $ER.f$ over $\mathrm{id}_{\operatorname{Spec} R}$ with $PP.P \,$ followed by $g$ equal to $\operatorname{Spec}(R\hookrightarrow L)$ followed by $PR$, with $m \cdot PR$ the unit section, and suppose $m$ is a unit in $L$. Then for every finite subset $s \subseteq L$ there are a finitely generated $\mathbb{Z}$-subalgebra $R'$ with $R \le R'$, $s \subseteq R'$ and $m$ a unit in $R'$, a fake elliptic curve $E'$ over $R'$, a morphism $g' : E'.A \to ER.A$ cartesian over $\operatorname{Spec}(R \hookrightarrow R')$ with the same four compatibilities (group law, $\Lambda$-action, and level in both directions), a section $P'$ of $E'.f$ over the identity with $P'$ followed by $g'$ equal to $\operatorname{Spec}(R\hookrightarrow R')$ followed by $PR$ and with $m \cdot P'$ the unit section, and a morphism $g_L : E.A \to E'.A$ cartesian over $\operatorname{Spec}(R' \hookrightarrow L)$, compatible with the group laws and $\Lambda$-equivariant, such that $PP.P$ followed by $g_L$ equals $\operatorname{Spec}(R' \hookrightarrow L)$ followed by $P'$. No level compatibility is asserted for $g_L$, and $P'$ is only asserted to be $m$-torsion, not to be a full level-$m$ structure.
--
--   This is a step in the spreading-out argument for fake elliptic curves with full level-$m$ structure: having descended the curve and its level-$m$ point to a finitely generated subalgebra $R$ of $L$, one enlarges $R$ to a finitely generated $R'$ containing a prescribed finite set and in which $m$ becomes invertible, base-changing the descended curve and section and factoring the original base change through the new one. It is used in the proof of [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_isUnit_isPullback_section_of_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    (L : Type) [CommRing L] (E : FakeEllipticCurve Λ N L) (PP : E.FullLevel m)
    (R : Subalgebra ℤ L) (hR : R.FG) (ER : FakeEllipticCurve Λ N ↥R)
    (g : E.A ⟶ ER.A) (hg : CategoryTheory.IsPullback g E.f ER.f (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hER :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ER.L.mul (t' ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ER.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' E.f),
        FactorsThrough E.lev P → ∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' E.f),
        (∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g) → FactorsThrough E.lev P))
    (PR : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) ER.f)
    (hPR : PP.P.1 ≫ g = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ PR.1)
    (hPRtor : nsmulPt ER.L (𝟙 (Spec (CommRingCat.of ↥R))) m PR = ER.L.one (𝟙 (Spec (CommRingCat.of ↥R))))
    (hm : IsUnit ((m : ℕ) : L)) (s : Finset L) :
    ∃ (R' : Subalgebra ℤ L) (_ : R'.FG) (hRR' : R ≤ R') (_ : (↑s : Set L) ⊆ R') (_ : IsUnit ((m : ℕ) : ↥R'))
      (E' : FakeEllipticCurve Λ N ↥R') (g' : E'.A ⟶ ER.A)
      (hg' : CategoryTheory.IsPullback g' E'.f ER.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom)))
      (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R'))) E'.f)
      (gL : E.A ⟶ E'.A) (hgL : CategoryTheory.IsPullback gL E.f E'.f (Spec.map (CommRingCat.ofHom R'.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ g' =
          (ER.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom))
            ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E'.act x ≫ g' = g' ≫ ER.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P : SchemeHomOver t' E'.f),
        FactorsThrough E'.lev P → ∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g') ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥R')) (P : SchemeHomOver t' E'.f),
        (∃ P₀ : T ⟶ ER.C, P₀ ≫ ER.lev = P.1 ≫ g') → FactorsThrough E'.lev P) ∧
      P'.1 ≫ g' = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ PR.1 ∧
      nsmulPt E'.L (𝟙 (Spec (CommRingCat.of ↥R'))) m P' = E'.L.one (𝟙 (Spec (CommRingCat.of ↥R'))) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gL =
          (E'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom R'.val.toRingHom))
            ⟨P.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ gL = gL ≫ E'.act x) ∧
      PP.P.1 ≫ gL = Spec.map (CommRingCat.ofHom R'.val.toRingHom) ≫ P'.1 := by sorry
