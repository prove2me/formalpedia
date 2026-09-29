-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7b5da8e6-443e-589d-9a25-8b962bade04c
-- title:
--   Spreading a full level-m structure to a finitely generated stage
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and primes $q,q'$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order not properly contained in another order), let $N,m\in\mathbb{N}$, let $L$ be a commutative ring, $E$ a fake elliptic curve over $L$ for $(\Lambda,N)$ carrying a full level-$m$ structure $PP$, and let $R\subseteq L$ be a finitely generated $\mathbb{Z}$-subalgebra with a fake elliptic curve $E_R$ over $R$. Assume given $g\colon E.A\to E_R.A$ making the square with $E.f$, $E_R.f$ and $\operatorname{Spec}$ of $R\hookrightarrow L$ cartesian, and compatible with the structures in four ways: $g$ carries the relative group law on $T$-points to that of $E_R$, it intertwines the $\Lambda$-actions, and a $T$-point of $E$ factors through the level map $E.\mathrm{lev}$ if and only if its image under $g$ factors through $E_R.\mathrm{lev}$. Assume further a section $PR$ of $E_R$ over $\operatorname{Spec}R$ with $m\cdot PR$ the unit section and with $PP.P$ mapping to $PR$ under $g$, that $m$ is a unit in $L$, and let $s\subseteq L$ be finite. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $R'\subseteq L$ with $R\le R'$ and $s\subseteq R'$, a fake elliptic curve $E'$ over $R'$, a morphism $g'\colon E'.A\to E_R.A$ exhibiting $E'$ as the base change of $E_R$ along $R\hookrightarrow R'$, and a section $P'$ of $E'$ over $\operatorname{Spec}R'$, such that $g'$ satisfies the same four compatibilities (group law, $\Lambda$-equivariance, level map in both directions), $P'$ maps to $PR$ under $g'$, and at every geometric point of $\operatorname{Spec}R'$ — that is, for every algebraically closed field $k$ and ring homomorphism $s_k\colon R'\to k$ — every $k$-point $Q$ of $E'$ killed by $m$ equals $x\cdot P'_{s_k}$ for some $x\in\Lambda$, and $x\cdot P'_{s_k}$ is the unit point precisely when $x\in m\Lambda$.
--
--   This is the spreading-out step for full level-$m$ structures on fake elliptic curves: a full level structure over a ring $L$ in which $m$ is invertible descends, together with any prescribed finite set of elements of $L$, to a finitely generated $\mathbb{Z}$-subalgebra, with the generation and annihilator properties holding at all geometric points of the finitely generated stage. It is used to obtain the finitely generated level over which the fine moduli description of the Shimura curve attached to $\Lambda$ can be tested.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_generates_annihilator_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
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
    ∃ (R' : Subalgebra ℤ L) (_ : R'.FG) (hRR' : R ≤ R') (_ : (↑s : Set L) ⊆ R')
      (E' : FakeEllipticCurve Λ N ↥R') (g' : E'.A ⟶ ER.A)
      (hg' : CategoryTheory.IsPullback g' E'.f ER.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom)))
      (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R'))) E'.f),
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
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R' →+* k) (Q : SchemeHomOver (geomPoint k sk) E'.f),
          nsmulPt E'.L (geomPoint k sk) m Q = E'.L.one (geomPoint k sk) →
            ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = Q) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ↥R' →+* k) (x : ↥Λ),
          pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k sk) = E'.L.one (geomPoint k sk) ↔
            ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) := by sorry
