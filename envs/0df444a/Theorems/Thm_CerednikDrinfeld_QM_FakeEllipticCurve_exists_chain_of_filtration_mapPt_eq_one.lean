-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_chain_of_filtration_mapPt_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/ce42b442-4260-5a2f-b9c1-28d4094ed7f5
-- title:
--   Chain of fake elliptic curves along a filtration of kerφ
-- statement:
--   Fix primes $q\ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be an order maximal among orders, and let $E$ be a fake elliptic curve of level $1$ over $\overline{\mathbb{Q}}$ (an abelian scheme of relative dimension $2$ with commutative relative group law, a $\Lambda$-action and level data, in the sense of `FakeEllipticCurve`). Let $t,n\in\mathbb{Z}$ with $t^2<4n$ and let $\varphi:E.A\to E.A$ be a morphism over the base which is additive on $T$-points, commutes with every $E.\mathrm{act}\,x$ for $x\in\Lambda$, and satisfies $\varphi(\varphi P)\cdot P^{n}=\varphi(P)^{t}$ for all points $P$. Let $e\in\mathbb{N}$, let $\ell_0,\dots,\ell_{e-1}$ be primes, and let $H_0\subseteq\cdots\subseteq H_e$ be sets of $\overline{\mathbb{Q}}$-points of $E$ (sections over the identity of $\mathrm{Spec}\,\overline{\mathbb{Q}}$) with $H_0=\{0\}$, $H_e=\ker\varphi(\overline{\mathbb{Q}})$, each $H_j$ finite and a subgroup stable under the $\Lambda$-action, such that $\#H_{j+1}=\ell_j^2\,\#H_j$, multiplication by $\ell_j$ sends $H_{j+1}$ into $H_j$, and whenever $\ell_j\in\{q,q'\}$, every $m\in\Lambda$ with $m\bar m=\ell_j k$ for some $k\in\mathbb{Z}$ sends $H_{j+1}$ into $H_j$. The conclusion asserts the existence of fake elliptic curves $C_0,\dots,C_e$ of level $1$ over $\overline{\mathbb{Q}}$ with $C_0=E$ and $C_e$ isomorphic to $E$ (via a scheme isomorphism over the base compatible with the group laws, the $\Lambda$-actions and the level structures), such that for each $j$ either $\ell_j\notin\{q,q'\}$ and there is an extra level structure $K$ at $\ell_j$ on $C_j$ (a finite flat closed subgroup of rank $\ell_j^2$, killed by $\ell_j$, $\Lambda$-stable and disjoint from the level) for which $C_{j+1}$ is a level isogeny quotient of $(C_j,K)$, that is, there are $\Lambda$-equivariant additive morphisms $\phi:C_j\to C_{j+1}$ and $\psi$ back with $\phi\psi$ and $\psi\phi$ the action of $\ell_j$, kernel of $\phi$ precisely the points factoring through $K$, and $\phi$ preserving level; or $\ell_j=q$ and $C_{j+1}$ is an Atkin–Lehner quotient of $C_j$ at $q$ (the same data with $\phi\psi=\psi\phi$ the action of $q$ and kernel of $\phi$ the points annihilated by all $m\in\Lambda$ with $q\mid m\bar m$); or $\ell_j=q'$ and the same at $q'$.
--
--   This realises the chain $E=A/H_0\to A/H_1\to\cdots\to A/H_e$ obtained by quotienting a fake elliptic curve successively by the terms of a $\Lambda$-stable filtration of the kernel of $\varphi$, each step being a quotient by a $\Lambda$-stable subgroup of order $\ell_j^2$ and hence either an isogeny with extra level structure at $\ell_j$ or, at the ramified primes $q,q'$, an Atkin–Lehner quotient. It feeds the statement `exists_chain_isLevelIsogeny_or_isAtkinLehnerQuotient_of_mapPt_mapPt_mul_zpow_eq_zpow`, and is assembled from the quotient construction `exists_quotient_forall_factorsThrough_iff_mem`, the two step-recognition results for level isogenies and Atkin–Lehner quotients, and `iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow` for the identification of the last term with $E$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_chain_of_filtration_mapPt_eq_one.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one
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
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t)

    (e : ℕ) (ℓ : Fin e → ℕ) (hℓ : ∀ j, (ℓ j).Prime)
    (H : Fin (e + 1) → Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f))
    (hH0 : H 0 = {E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))})
    (hHe : H (Fin.last e) = {P | mapPt φ hφ P = E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ))))})
    (hmono : ∀ j : Fin e, H j.castSucc ⊆ H j.succ)
    (hfin : ∀ j, (H j).Finite)
    (hone : ∀ j, E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H j)
    (hmul : ∀ j P Q, P ∈ H j → Q ∈ H j → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H j)
    (hinv : ∀ j P, P ∈ H j → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H j)
    (hstab : ∀ j (x : ↥Λ) P, P ∈ H j → pushPt (E.act x) (E.act_over x) P ∈ H j)
    (hcard : ∀ j : Fin e, Nat.card (H j.succ) = ℓ j ^ 2 * Nat.card (H j.castSucc))
    (htors : ∀ (j : Fin e) P, P ∈ H j.succ →
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (ℓ j) P ∈ H j.castSucc)
    (hram : ∀ j : Fin e, (ℓ j = q ∨ ℓ j = q') → ∀ P, P ∈ H j.succ →
      ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ j : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P ∈ H j.castSucc) :
    ∃ C : Fin (e + 1) → FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ),
      C 0 = E ∧ FakeEllipticCurve.Iso (C (Fin.last e)) E ∧
      ∀ j : Fin e,
        (ℓ j ≠ q ∧ ℓ j ≠ q' ∧ ∃ K : (C j.castSucc).ExtraLevel (ℓ j),
            FakeEllipticCurve.IsLevelIsogeny (ℓ j)
              (⟨C j.castSucc, K⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 (ℓ j) (AlgebraicClosure ℚ)) (C j.succ)) ∨
        (ℓ j = q ∧ FakeEllipticCurve.IsAtkinLehnerQuotient q (C j.castSucc) (C j.succ)) ∨
        (ℓ j = q' ∧ FakeEllipticCurve.IsAtkinLehnerQuotient q' (C j.castSucc) (C j.succ)) := by sorry
