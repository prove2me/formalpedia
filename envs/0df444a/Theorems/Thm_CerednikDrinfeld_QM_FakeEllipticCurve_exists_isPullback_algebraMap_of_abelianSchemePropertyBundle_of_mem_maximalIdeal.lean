-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b237c898-55b6-5f6c-be3d-311ac08d5702
-- title:
--   Good reduction of the surface extends a fake elliptic curve
-- statement:
--   Fix natural numbers $N$ and primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order (containing $1$, closed under multiplication, $\mathbb Q$-spanning, finitely generated, and maximal among such). Let $R$ be a discrete valuation domain with fraction field $K$, let $p$ be a prime whose image in $R$ lies in the maximal ideal, and suppose $N$, $q$, $q'$ are units of $R$. Let $E_0$ be a fake elliptic curve over $K$ for $\Lambda$ and level $N$. Suppose given a scheme $\mathcal A$ with a morphism $f_{\mathcal A}\colon\mathcal A\to\operatorname{Spec} R$, a commutative relative group law $L_{\mathcal A}$ on the $T$-points of $f_{\mathcal A}$, and `AbelianSchemePropertyBundle` for $f_{\mathcal A}$ ($f_{\mathcal A}$ smooth and proper, with connected fibres and some relative group law), together with $g\colon E_0.A\to\mathcal A$ making the square over $\operatorname{Spec} K\to\operatorname{Spec} R$ cartesian and compatible with the two group laws on points over any $K$-scheme. Then there exists a fake elliptic curve $\mathcal E$ over $R$ for $\Lambda$ and level $N$ with `FakeEllipticCurve.IsPullback (algebraMap R K) 𝓔 E₀`: some morphism $E_0.A\to\mathcal E.A$ forms a cartesian square over $\operatorname{Spec} K\to\operatorname{Spec} R$, is compatible with the group laws on points, commutes with the $\Lambda$-actions, and sends points factoring through the level structure of $E_0$ to points factoring through that of $\mathcal E$.
--
--   This is the good-reduction criterion for fake elliptic curves: if the abelian surface underlying a fake elliptic curve over $K$ admits an abelian-scheme extension over the discrete valuation ring $R$ (residue characteristic prime to $Nqq'$), then the quaternionic action and the level structure extend as well, so the whole moduli datum descends to $R$. It is used in the passage to the integral model over an intersection of valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_algebraMap_of_abelianSchemePropertyBundle_of_mem_maximalIdeal
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} [Fact p.Prime] (hp : ((p : ℕ) : R) ∈ IsLocalRing.maximalIdeal R)
    (hN : IsUnit ((N : ℕ) : R)) (hq : IsUnit ((q : ℕ) : R)) (hq' : IsUnit ((q' : ℕ) : R))
    (E₀ : FakeEllipticCurve Λ N K)
    {𝒜 : Scheme.{u}} {f𝒜 : 𝒜 ⟶ Spec (CommRingCat.of R)} (L𝒜 : RelativeGroupLaw R f𝒜) (hc : L𝒜.IsCommutative)
    (h𝒜 : AbelianSchemePropertyBundle R f𝒜)
    (g : E₀.A ⟶ 𝒜) (hg : CategoryTheory.IsPullback g E₀.f f𝒜 (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' x y).1 ≫ g =
        (L𝒜.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) :
    ∃ 𝓔 : FakeEllipticCurve Λ N R, FakeEllipticCurve.IsPullback (algebraMap R K) 𝓔 E₀ := by sorry
