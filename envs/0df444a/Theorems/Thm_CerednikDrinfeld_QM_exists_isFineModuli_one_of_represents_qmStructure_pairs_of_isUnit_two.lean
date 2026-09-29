-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_represents_qmStructure_pairs_of_isUnit_two
-- name    : CerednikDrinfeld.QM.exists_isFineModuli_one_of_represents_qmStructure_pairs_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/4c38abe5-ab40-5629-adb2-79135a02c0e2
-- title:
--   Fine moduli for full-level fake elliptic curves from QM pairs
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, is a division algebra over the completion at $v$ exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and no strictly larger order contains it); let $m\geq 3$ and let $\mathcal{O}$ be a commutative ring in which both $m$ and $2$ are units. Fix $\mu\in\Lambda$ with $\mu^{2}=-(qq')\cdot 1$, a map $\mathrm{star}:\Lambda\to\Lambda$ with $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x$, and $\beta:\mathrm{Fin}(2\cdot 2)\to\Lambda$ such that every element of $\Lambda$ is uniquely an integral combination $\sum_j c_j\beta_j$. Let $M_1$ be a scheme with a morphism $\pi_1:M_1\to\operatorname{Spec}\mathcal{O}$, and let $\mathrm{ptQ}$ assign, to each commutative ring $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$, each polarised abelian scheme $X$ over $S$ of relative fibre dimension $2$ with $m$-torsion basis and geometric fibrewise $H^{0}$-rank $36$ for its invertible very ample module, and each `QMStructure` $t$ for $(\Lambda,\mathrm{star},\beta)$ on $X$, a morphism $\operatorname{Spec}S\to M_1$ over $s$. Assume $\mathrm{ptQ}$ is constant on `QMStructure.Iso`-classes, is natural along `QMStructure.IsPullback` (if $\operatorname{Spec}\varphi$ followed by $s$ equals $s'$, the value at the pulled-back datum is $\operatorname{Spec}\varphi$ followed by the value at the original one), is surjective onto the morphisms over $s$, and satisfies: equal values imply `QMStructure.Iso`. Then there is a rule $\mathrm{ptF}_1$ assigning to each $S$, each $s$ and each pair consisting of a fake elliptic curve for $\Lambda$ with $N=1$ together with a full level-$m$ structure, a morphism over $s$, such that `IsFineModuli Λ 1 m M₁ π₁ ptF₁` holds: $\mathrm{ptF}_1$ is constant on `WithFullLevel.Iso`-classes, natural along `WithFullLevel.IsPullback`, surjective onto morphisms over $s$, and injective up to `WithFullLevel.Iso`.
--
--   This is the transport step in the construction of the integral model of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$: a scheme that finely represents pairs (polarised abelian surface with full level-$m$ structure, quaternionic multiplication) also finely represents fake elliptic curves with trivial $\Gamma_0$-level and full level $m$, the dictionary between the two moduli problems being available once $2$ is invertible on the base. It feeds the subsequent construction of fine moduli schemes under local theta-type and finite-type hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_represents_qmStructure_pairs_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem CerednikDrinfeld.QM.exists_isFineModuli_one_of_represents_qmStructure_pairs_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪)) (h2 : IsUnit (2 : 𝒪))
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (M₁ : Scheme.{0}) (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪))
    (ptQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → SchemeHomOver s π₁)
    (hiso : (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
          (X X' : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        QMStructure.Iso t t' → ptQ S s X t = ptQ S s X' t'))
    (hpb : (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
          (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        QMStructure.IsPullback φ t t' → (ptQ S' s' X' t').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptQ S s X t).1))
    (hsurj : (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s π₁),
        ∃ (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X), ptQ S s X t = x))
    (hinj : (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
          (X X' : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X'),
        ptQ S s X t = ptQ S s X' t' → QMStructure.Iso t t')) :
    ∃ ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁,
      IsFineModuli Λ 1 m M₁ π₁ ptF₁ := by sorry
