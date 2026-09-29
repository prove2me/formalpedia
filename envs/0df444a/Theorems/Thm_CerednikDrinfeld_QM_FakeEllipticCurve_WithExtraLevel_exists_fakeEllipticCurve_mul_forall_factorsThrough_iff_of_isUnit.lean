-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/b4cbb617-6393-581d-b267-b471befea131
-- title:
--   Merging level N and extra level ℓ structures
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$ with $\gcd(N,\ell)=1$, and a commutative ring $S$ in which the image of $N\ell$ is a unit. Let $u$ be a pair consisting of a fake elliptic curve $u.1$ of level $N$ over $S$ — an $S$-scheme $u.1.f\colon u.1.A\to\operatorname{Spec} S$ carrying a commutative relative group law $u.1.L$ on its functor of points, an abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action $u.1.act$ by endomorphisms over $S$, and a level structure $u.1.lev$ — together with an extra level structure $u.2$ at $\ell$, whose datum is a closed immersion $u.2.levK\colon u.2.K\to u.1.A$ subject to the subgroup, $\ell$-torsion, $\Lambda$-stability, disjointness from $u.1.lev$, finite flat rank $\ell^2$ and geometric fibre $(\mathbb{Z}/\ell)^2$ conditions. The assertion is that there exist a fake elliptic curve $E'$ of level $N\ell$ over $S$ and an isomorphism $e\colon u.1.A\cong E'.A$ with $E'.f\circ e=u.1.f$, such that postcomposition with $e$ on $T$-points (for $T$ a scheme over $\operatorname{Spec} S$) carries $u.1.L$-multiplication to $E'.L$-multiplication, $e$ intertwines the two $\Lambda$-actions ($e\circ u.1.act\,x=E'.act\,x\circ e$ for all $x\in\Lambda$), and, for every $T\to\operatorname{Spec} S$ and every $T$-point $P$ of $u.1.A$ over it: $P$ factors through $u.1.lev$ if and only if $e\circ P$ factors through $E'.lev$ and is killed by $N$ in $E'.L$, while $P$ factors through $u.2.levK$ if and only if $e\circ P$ factors through $E'.lev$ and is killed by $\ell$.
--
--   This is the combination step for level structures on fake elliptic curves: a level-$N$ structure together with an independent extra level at $\ell$, with $N\ell$ invertible on the base, is the same as a level-$N\ell$ structure, whose subgroup is the direct sum of the two given ones, the original pieces being recovered as the $N$- and $\ell$-torsion inside it. It is used in the construction of coarse moduli for fake elliptic curves of level $N\ell$, via [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ E' : FakeEllipticCurve Λ (N * ℓ) S, ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.1.lev P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.2.levK P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t) := by sorry
