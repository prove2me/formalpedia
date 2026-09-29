-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_universallyClosed_of_represents_of_finiteType
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.universallyClosed_of_represents_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/51c0a167-8ff7-5fbf-b0ac-00e2cd8d4b12
-- title:
--   Universal closedness of a finite-type scheme representing QM structures
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathbb{Q}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $\mu \in \Lambda$ with $\mu^{2} = -qq'$, $\mathrm{star} : \Lambda \to \Lambda$ a map satisfying $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x$, and $\beta : \mathrm{Fin}\,4 \to \Lambda$ a family such that every $x \in \Lambda$ is uniquely $\sum_j c_j \beta_j$ with $c_j \in \mathbb{Z}$. Let $d,m$ be naturals with $m \geq 3$, let $R$ be a commutative ring of finite type over $\mathbb{Z}$ in which $m$ is invertible, and let $X$ be a polarised abelian scheme over $R$ of relative fibre dimension $2$, geometric $H^{0}$-rank $d$ of the polarising invertible module and full $m$-level structure. Let $\zeta : Z \to \operatorname{Spec} R$ be a morphism of schemes together with a family $\mathrm{ptZ}$ assigning, to each commutative ring $T$, ring homomorphism $\varphi : R \to T$, polarised abelian scheme $X'$ over $T$ exhibited as a base change of $X$ along $\varphi$, and quaternionic multiplication structure on $X'$ for the data $(\Lambda,\mathrm{star},\beta)$ — that is, an action of $\Lambda$ by endomorphisms of $X'$ over $T$ which is additive, (anti)multiplicative, compatible with the group law, satisfies the reduced-trace condition on geometric tangent spaces, carries a point $P$ over the base whose images under $\beta_j$ are the level points of $X'$, and for which the polarising module is locally on the base the triple tensor power of a canonical polarisation datum for $\mathrm{star}$ — a morphism $\operatorname{Spec} T \to Z$ whose composite with $\zeta$ is $\operatorname{Spec}\varphi$. Assume $\mathrm{ptZ}$ is natural in $T$ (compatible with ring maps $\psi$ and pullbacks of QM structures), surjective and injective on QM structures over each such $T$, and assume $\zeta$ is quasi-compact and locally of finite type. Then $\zeta$ is universally closed.
--
--   This is the properness half of the representability package for the moduli problem of polarised abelian surfaces with quaternionic multiplication by a maximal order in an indefinite quaternion algebra ramified exactly at $q,q'$, in the hypothesis form where the representing scheme is given together with its functor of points. It is stated over a base of finite type over $\mathbb{Z}$ so that the discrete valuation ring valuative criterion applies, the lifting step being extension of QM structures across a discrete valuation ring, and it feeds the construction of a finite representing scheme for these Shimura-curve-type moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_universallyClosed_of_represents_of_finiteType.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicGeometry

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.universallyClosed_of_represents_of_finiteType
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
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
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s''))
    (hqc : QuasiCompact ζ) (hlft : LocallyOfFiniteType ζ) :
    UniversallyClosed ζ := by sorry
