-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/3ce41fbb-bcfa-5c70-9c13-0a8ff81d212a
-- title:
--   Splitting a level-Nℓ fake elliptic curve into level N and extra level ℓ
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$ with $\gcd(N,\ell)=1$, and a commutative ring $S$ in which the image of $N\ell$ is a unit. Let $E'$ be a fake elliptic curve of level $N\ell$ for $\Lambda$ over $S$, i.e. a scheme $E'.A$ with a structure morphism $E'.f$ to $\operatorname{Spec} S$, a commutative relative group law $E'.L$ on $T$-points (morphisms $\varphi : T \to E'.A$ over $\operatorname{Spec} S$), a $\Lambda$-action and a level morphism $E'.\mathrm{lev}$, subject to the remaining axioms of the structure. The assertion is that there exist a fake elliptic curve $u.1$ of level $N$ for $\Lambda$ over $S$ together with an extra level structure $u.2$ at $\ell$ on it, and an isomorphism of schemes $e : u.1.A \cong E'.A$ with $e$ followed by $E'.f$ equal to $u.1.f$, such that: transport along $e$ (sending a $T$-point $P$ of $u.1.A$ to $P$ followed by $e$) is a homomorphism for the two relative group laws, on $T$-points over every $t : T \to \operatorname{Spec} S$; $e$ intertwines the actions, $u.1.\mathrm{act}(x)$ followed by $e$ equalling $e$ followed by $E'.\mathrm{act}(x)$ for all $x \in \Lambda$; and, for all $t : T \to \operatorname{Spec} S$ and all $T$-points $P$ of $u.1.A$, $P$ factors through $u.1.\mathrm{lev}$ if and only if the transported point factors through $E'.\mathrm{lev}$ and is killed by $N$ for $E'.L$, while $P$ factors through the extra level morphism $u.2.\mathrm{levK}$ if and only if the transported point factors through $E'.\mathrm{lev}$ and is killed by $\ell$.
--
--   This is the splitting of a level-$N\ell$ structure on a fake elliptic curve into its $N$-part and its $\ell$-part, the level-$N$ structure being the $N$-torsion of the given one and the extra level at $\ell$ its $\ell$-torsion, under the assumption that $N\ell$ is invertible on the base. It is used in the comparison of coarse moduli for $\Lambda$-level structures, namely by [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_forall_factorsThrough_iff_of_mul_of_isUnit
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : S)) (E' : FakeEllipticCurve Λ (N * ℓ) S) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S, ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.1.lev P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.2.levK P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t) := by sorry
