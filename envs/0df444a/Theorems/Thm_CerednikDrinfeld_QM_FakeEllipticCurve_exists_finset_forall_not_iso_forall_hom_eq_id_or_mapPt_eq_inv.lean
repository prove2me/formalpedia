-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e950c623-4ec7-50c6-92de-85497618e5d1
-- title:
--   Cofinite rigidity of fake elliptic curves over ℚ̄
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element a unit) exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is the only order containing it; and let $N$ be a nonzero natural number. Then there are $m\in\mathbb{N}$ and a family $S:\mathrm{Fin}\,m\to$ `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` with the following property. Let $E$ be a fake elliptic curve of level $N$ over $\overline{\mathbb{Q}}$ in the sense of the structure `FakeEllipticCurve` which satisfies `FakeEllipticCurve.Iso E (S j)` for no $j$. Let $e : E.A\cong E.A$ be an isomorphism of schemes with $e.\mathrm{hom}$ followed by $E.f$ equal to $E.f$, such that for every scheme $T$, every $t : T\to\operatorname{Spec}\overline{\mathbb{Q}}$ and all $T$-points $P,Q$ of $E$ over $t$ one has $\mathrm{mapPt}(e.\mathrm{hom})(E.L.\mathrm{mul}\,t\,P\,Q)=E.L.\mathrm{mul}\,t\,(\mathrm{mapPt}(e.\mathrm{hom})P)(\mathrm{mapPt}(e.\mathrm{hom})Q)$, where $\mathrm{mapPt}$ sends a point $P$ to $P$ followed by $e.\mathrm{hom}$, and such that $E.\mathrm{act}\,x$ followed by $e.\mathrm{hom}$ equals $e.\mathrm{hom}$ followed by $E.\mathrm{act}\,x$ for every $x\in\Lambda$. Then either $e.\mathrm{hom}=\mathbb{1}_{E.A}$, or $\mathrm{mapPt}(e.\mathrm{hom})P=E.L.\mathrm{inv}\,t\,P$ for all $T$, all $t$ and all points $P$. No compatibility of $e$ with the level datum $E.\mathrm{lev}$ is required, although such compatibility is part of the relation `FakeEllipticCurve.Iso` defining the exceptional list.
--
--   This is the rigidity statement that the group of $\Lambda$-equivariant automorphisms of a fake elliptic curve over $\overline{\mathbb{Q}}$ respecting the group law is $\{\pm 1\}$, outside a finite list of isomorphism classes (those with extra automorphisms, coming from quaternionic abelian surfaces whose $\Lambda$-endomorphism ring is an order containing units other than $\pm 1$). It is used in the construction of moduli of fake elliptic curves with extra level structure, where rigidity is needed to make level data transport along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_hom_eq_id_or_mapPt_eq_inv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] :
    ∃ (m : ℕ) (S : Fin m → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ), (∀ j : Fin m, ¬ FakeEllipticCurve.Iso E (S j)) →
        ∀ (e : E.A ≅ E.A) (he : e.hom ≫ E.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
              mapPt e.hom he (E.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
          (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E.act x) →
          e.hom = 𝟙 E.A ∨
            ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
              mapPt e.hom he P = E.L.inv t P := by sorry
