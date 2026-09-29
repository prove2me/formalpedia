-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.formallyUnramified_of_represents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/2c6c64b1-2008-57bf-b5f5-b7598728a379
-- title:
--   Formal unramifiedness of a scheme representing QM structures
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, let $star:\Lambda\to\Lambda$ satisfy $\mu\,star(x)=\bar{x}\mu$ for all $x\in\Lambda$, and let $\beta:\mathrm{Fin}\,4\to\Lambda$ be such that each $x\in\Lambda$ is a unique integral combination $\sum_j c_j\beta_j$. Let $d,m\in\mathbb{N}$ with $3\le m$, let $R$ be a commutative ring in which $m$ is a unit, and let $X$ be a polarised abelian scheme of relative dimension $2$, fibre degree $d$ and full level $m$ over $R$. Let $\zeta:Z\to\operatorname{Spec}R$ be a morphism of schemes together with an assignment $\mathrm{pt}_Z$ sending each commutative ring $T$, ring map $\varphi:R\to T$, polarised abelian scheme $X'$ over $T$ exhibited as a base change of $X$ along $\varphi$ (in the sense of `PolarisedAbelianScheme.IsPullback`), and QM structure on $X'$ for the data $(\Lambda,star,\beta)$, to a morphism $\operatorname{Spec}T\to Z$ whose composite with $\zeta$ is $\operatorname{Spec}\varphi$. Assume $\mathrm{pt}_Z$ is natural in further base changes $\psi:T\to T'$ compatible with pullbacks of QM structures, and that for each fixed $\varphi$ and $X'$ it is surjective onto such morphisms over $\operatorname{Spec}\varphi$ and injective on QM structures. Then $\zeta$ is formally unramified.
--
--   This is the rigidity step for quaternionic multiplication data with full level structure of order $m\ge 3$: any scheme representing the functor of QM structures on base changes of a fixed polarised abelian surface with full level $m$ is formally unramified over the base, because a QM structure admits no nontrivial infinitesimal automorphisms once the level-$m$ points are fixed. It feeds the construction of the associated moduli scheme, being used in the finiteness and representability statement [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_finite_represents_of_isUnit_two_of_finiteType`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_finite_represents_of_isUnit_two_of_finiteType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_formallyUnramified_of_represents.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.formallyUnramified_of_represents
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ)
    (hnat : (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1))
    (hsurj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z))
    (hinj : (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'')) :
    FormallyUnramified ζ := by sorry
