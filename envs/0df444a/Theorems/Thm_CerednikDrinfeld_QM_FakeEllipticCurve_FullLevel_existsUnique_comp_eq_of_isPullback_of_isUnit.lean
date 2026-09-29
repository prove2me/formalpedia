-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_of_isPullback_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/e553253f-0669-51ed-aee3-0cb0fbc48b3a
-- title:
--   Unique extension of full level-m structures over a DVR
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and natural numbers $N$ and $m$. Let $R$ be a discrete valuation ring (a commutative domain) with fraction field $K$, realised through an $R$-algebra structure on the field $K$ making $K$ the fraction field of $R$, and suppose the image of $m$ in $R$ is a unit. Let $\mathcal{A}$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $R$ and $E$ one over $K$, each consisting of a scheme with a morphism to the spectrum of the base, a commutative relative group law on its functor of points, an abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and the multiplication of $\Lambda$, a trace condition, and level-$N$ data. Let $g : E.A \to \mathcal{A}.A$ be a morphism making the square with $E.f$, $\mathcal{A}.f$ and $\operatorname{Spec}$ of $R \to K$ cartesian, such that composing with $g$ carries the product of two $T$-points of $E$ over any $t' : T \to \operatorname{Spec} K$ to the product of their images as $T$-points of $\mathcal{A}$ over $t'$ followed by $\operatorname{Spec}(R \to K)$, and such that $E.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $\mathcal{A}.\mathrm{act}\,x$ for every $x \in \Lambda$. Let $P_K$ be a full level-$m$ structure on $E$: a section of $E.f$ over the identity of $\operatorname{Spec} K$ which is killed by $m$ for the group law, whose $\Lambda$-orbit, after base change along any ring map from $K$ to an algebraically closed field $k$, exhausts all $m$-torsion points over that geometric base point, and for which $\mathrm{act}\,x$ sends the base-changed section to the unit point exactly when $x \in m\Lambda$. Then there is exactly one full level-$m$ structure $P$ on $\mathcal{A}$ whose underlying section satisfies $P_K$ followed by $g$ equals $\operatorname{Spec}(R \to K)$ followed by $P$.
--
--   This is the statement that a full level-$m$ structure with $m$ invertible on the base extends uniquely from the generic fibre to a fake elliptic curve over a discrete valuation ring, the rigidity input making the fine moduli problem with level structure prime to the residue characteristic behave well under specialisation. It is used in constructing pullbacks of pairs (fake elliptic curve, full level structure) along $R \to K$ for complete discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_of_isPullback_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_of_isPullback_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] (hm : IsUnit ((m : ℕ) : R))
    (𝒜 : FakeEllipticCurve Λ N R) (E : FakeEllipticCurve Λ N K)
    (g : E.A ⟶ 𝒜.A) (hg : CategoryTheory.IsPullback g E.f 𝒜.f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ g =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E.act x ≫ g = g ≫ 𝒜.act x)
    (PK : E.FullLevel m) :
    ∃! P : 𝒜.FullLevel m, (PK.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (P.P).1 := by sorry
