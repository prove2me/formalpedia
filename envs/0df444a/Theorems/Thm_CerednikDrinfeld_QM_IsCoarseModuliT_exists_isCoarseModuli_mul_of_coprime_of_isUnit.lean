-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isCoarseModuli_mul_of_coprime_of_isUnit
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/aaec707f-3fee-58f5-b9ce-c599c57eaa03
-- title:
--   Coarse moduli of (N,ℓ)-pairs gives level Nℓ
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, and natural numbers $N,\ell$ with $\gcd(N,\ell)=1$. Let $B$ be a commutative ring in which the image of $N\ell$ is a unit, let $Y$ be a scheme and $\pi_Y : Y \to \operatorname{Spec} B$ a morphism, and let $\mathrm{pt}_T$ be a rule assigning to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every pair $u$ consisting of a `FakeEllipticCurve` $u.1$ of level $N$ over $S$ together with an extra $\ell$-level structure $u.2$, a morphism $\operatorname{Spec} S \to Y$ whose composite with $\pi_Y$ is $s$; assume `IsCoarseModuliT Λ N ℓ Y πY ptT`, i.e. $\mathrm{pt}_T$ is constant on isomorphism classes of pairs, compatible with base change along ring homomorphisms, bijective on geometric points over algebraically closed fields, and universal among such rules. Then there is a rule $\mathrm{pt}$ assigning to every $S$, every $s$ and every `FakeEllipticCurve` $E'$ of level $N\ell$ over $S$ a morphism $\operatorname{Spec} S \to Y$ over $s$, such that `IsCoarseModuli Λ (N * ℓ) Y πY pt` holds (the same five conditions with level-$N\ell$ curves in place of pairs), and such that $\mathrm{pt}\,S\,s\,E' = \mathrm{pt}_T\,S\,s\,u$ whenever $u$ splits $E'$, meaning: there is an isomorphism $e : u.1.A \cong E'.A$ over $S$ ($e$ followed by $E'.f$ equals $u.1.f$) which transports the relative group law of $u.1$ to that of $E'$ on $T$-points, satisfies $u.1.\mathrm{act}\,x$ followed by $e$ $=$ $e$ followed by $E'.\mathrm{act}\,x$ for all $x \in \Lambda$, and for which, for every $t : T \to \operatorname{Spec} S$ and every point $P$ over $t$, $P$ factors through $u.1.\mathrm{lev}$ precisely when its image under $e$ factors through $E'.\mathrm{lev}$ and is killed by $N$ in $E'.L$, and $P$ factors through $u.2.\mathrm{levK}$ precisely when its image factors through $E'.\mathrm{lev}$ and is killed by $\ell$.
--
--   This is the comparison, for coprime $N$ and $\ell$ invertible on the base, between the moduli problem of fake elliptic curves of level $N$ equipped with an extra $\ell$-structure and the moduli problem at the single level $N\ell$: one coarse moduli scheme serves both, with matching point maps. It is used in establishing integrality properties of the resulting coarse moduli scheme for squarefree level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_isCoarseModuli_mul_of_coprime_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    {B : Type} [CommRing B] (hu : IsUnit ((N * ℓ : ℕ) : B))
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptT) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
        FakeEllipticCurve Λ (N * ℓ) S → SchemeHomOver s πY,
      IsCoarseModuli Λ (N * ℓ) Y πY pt ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (E' : FakeEllipticCurve Λ (N * ℓ) S),
        (∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
            mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
          (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
            FactorsThrough u.1.lev P ↔
              FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
            FactorsThrough u.2.levK P ↔
              FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t)) →
        pt S s E' = ptT S s u := by sorry
