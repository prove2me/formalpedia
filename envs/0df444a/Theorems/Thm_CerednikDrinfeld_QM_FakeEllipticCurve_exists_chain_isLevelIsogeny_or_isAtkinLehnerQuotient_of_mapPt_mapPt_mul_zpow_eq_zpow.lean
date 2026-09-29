-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_chain_isLevelIsogeny_or_isAtkinLehnerQuotient_of_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_isLevelIsogeny_or_isAtkinLehnerQuotient_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/8b069c37-51b7-5ebe-bee2-67789590c28f
-- title:
--   Chain decomposition of a CM endomorphism of a fake elliptic curve
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, and let $E$ be a fake elliptic curve of level $1$ for $\Lambda$ over $\overline{\mathbb{Q}}$, i.e. a scheme $E.A$ over $\mathrm{Spec}\,\overline{\mathbb{Q}}$ with a commutative relative group law $E.L$, abelian-scheme property bundle, fibres of Krull dimension $2$, an action of $\Lambda$ by endomorphisms additive in the point and in $\Lambda$, multiplicative for the ring structure and satisfying the trace condition on tangent spaces, together with its level data. Let $t,n \in \mathbb{Z}$ with $t^2 < 4n$, and let $\varphi : E.A \to E.A$ be a morphism over the base which is additive on $T$-valued points, commutes with every $\Lambda$-action $E.\mathrm{act}\,x$, and satisfies $\varphi(\varphi P)\cdot P^{n} = \varphi(P)^{t}$ in the commutative group of $T$-valued points, for all $T$ and all $P$. Then there are $e \in \mathbb{N}$, primes $\ell_0,\dots,\ell_{e-1}$ with $\prod_j \ell_j = n$ in $\mathbb{Z}$, and fake elliptic curves $C_0,\dots,C_e$ of level $1$ for $\Lambda$ over $\overline{\mathbb{Q}}$ with $C_0 = E$ and $C_e$ isomorphic to $E$ (an isomorphism of the underlying schemes over the base compatible with the group laws, the $\Lambda$-actions and the level structures), such that for each $j$ one of the following holds: $\ell_j \neq q$, $\ell_j \neq q'$ and there is an extra level structure $K$ of level $\ell_j$ on $C_j$ (a closed immersion into $C_j.A$ whose points form a $\Lambda$-stable subgroup of $\ell_j$-torsion meeting the level structure trivially, finite flat of rank $\ell_j^2$ with geometric fibres $(\mathbb{Z}/\ell_j)^2$) with $C_{j+1}$ a level-$\ell_j$ isogeny quotient of $(C_j,K)$, meaning there are mutually dual $\Lambda$-equivariant additive morphisms between $C_j.A$ and $C_{j+1}.A$ whose composites are the action of $\ell_j$ (when $\ell_j \in \Lambda$), the first having kernel on points exactly those factoring through $K$ and preserving level structures; or $\ell_j = q$, respectively $\ell_j = q'$, and $C_{j+1}$ is an Atkin–Lehner quotient of $C_j$ at that prime $r$, the same package of mutually dual $\Lambda$-equivariant additive morphisms with composites the action of $r$, but with the kernel of the first described as those points killed by every $m \in \Lambda$ with $m\,\bar m = rn$ for some $n \in \mathbb{Z}$.
--
--   This is the step-by-step filtration of an endomorphism $\varphi$ of a fake elliptic curve satisfying the quadratic relation $\varphi^2 - t\varphi + n = 0$ with $t^2 < 4n$ (a complex multiplication, so an isogeny of degree $n^2$): the $\Lambda$-stable kernel is refined into simple subquotients, which are lines for $\Lambda/\ell\Lambda \cong M_2(\mathbb{F}_\ell)$ at primes $\ell$ away from the ramification, and the Atkin–Lehner kernels at $q$ and $q'$. It feeds the finiteness statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow), which bounds the fake elliptic curves admitting such extra endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_chain_isLevelIsogeny_or_isAtkinLehnerQuotient_of_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_isLevelIsogeny_or_isAtkinLehnerQuotient_of_mapPt_mapPt_mul_zpow_eq_zpow
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (t n : ℤ) (htn : t ^ 2 < 4 * n)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    ∃ (e : ℕ) (ℓ : Fin e → ℕ) (C : Fin (e + 1) → FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)),
      (∀ j, (ℓ j).Prime) ∧ (∏ j, (ℓ j : ℤ)) = n ∧ C 0 = E ∧ FakeEllipticCurve.Iso (C (Fin.last e)) E ∧
      ∀ j : Fin e,
        (ℓ j ≠ q ∧ ℓ j ≠ q' ∧ ∃ K : (C j.castSucc).ExtraLevel (ℓ j),
            FakeEllipticCurve.IsLevelIsogeny (ℓ j)
              (⟨C j.castSucc, K⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 (ℓ j) (AlgebraicClosure ℚ)) (C j.succ)) ∨
        (ℓ j = q ∧ FakeEllipticCurve.IsAtkinLehnerQuotient q (C j.castSucc) (C j.succ)) ∨
        (ℓ j = q' ∧ FakeEllipticCurve.IsAtkinLehnerQuotient q' (C j.castSucc) (C j.succ)) := by sorry
