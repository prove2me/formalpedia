-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_represents_isSeparated_quasiCompact_locallyOfFinitePresentation_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_isSeparated_quasiCompact_locallyOfFinitePresentation_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/96ad6b57-1799-5afc-9ca9-78037acaaf2d
-- title:
--   Representability of QM structures by a separated quasi-compact morphism
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb Q$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders for inclusion, let $\mu\in\Lambda$ satisfy $\mu^2=-qq'$, let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar x\mu$ for all $x$, and let $\beta:\mathrm{Fin}\,4\to\Lambda$ be such that each $x\in\Lambda$ is uniquely $\sum_j c_j\beta_j$ with $c\in\mathbb Z^4$. Let $d,m$ be naturals with $m\ge 3$, let $R$ be a commutative ring in which $m$ and $2$ are units, and let $X$ be a polarised abelian scheme of relative dimension $2$, degree $d$ and full level $m$ over $\operatorname{Spec}R$ in the sense of `PolarisedAbelianScheme` (commutative relative group law with the `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $2$, four $m$-torsion sections that are independent and generate the $m$-torsion of every geometrically algebraically closed fibre, and an invertible module `pol` which is a closed immersion by sections over the base with geometric fibre $H^0$-rank $d$). Then there exist a scheme $Z$, a morphism $\zeta:Z\to\operatorname{Spec}R$, and a rule $\mathrm{pt}_Z$ assigning to every commutative ring $T$, ring homomorphism $\varphi:R\to T$, polarised abelian scheme $X'$ over $T$ with $X'$ a pullback of $X$ along $\varphi$, and every $\mathrm{QMStructure}$ on $X'$ for the data $(\Lambda,\mathrm{star},\beta)$ (an action of $\Lambda$ on the total space over the base, anti-multiplicative, additive and compatible with the group law, satisfying the tangent-trace condition for reduced traces, together with a section whose images under $\beta_j$ are the level-$m$ sections, and an invertible module with `IsCanonicalPolData` whose third tensor power is locally isomorphic on the base to `pol`), a morphism $\operatorname{Spec}T\to Z$ whose composite with $\zeta$ is $\operatorname{Spec}\varphi$, such that: $\zeta$ is separated, quasi-compact and locally of finite presentation; $\mathrm{pt}_Z$ is natural, in that for $\psi:T\to T'$ with $\psi\circ\varphi=\varphi'$ and QM structures $s',s''$ on pullbacks $X',X''$ with $s''$ a pullback of $s'$ along $\psi$, the point attached to $s''$ is $\operatorname{Spec}\psi$ followed by the point attached to $s'$; for each $(T,\varphi,X')$ every morphism $\operatorname{Spec}T\to Z$ over $\operatorname{Spec}\varphi$ arises as $\mathrm{pt}_Z$ of some QM structure on $X'$; and two QM structures on $X'$ giving the same point coincide.
--
--   This is the existence half of the representability statement for quaternionic multiplication structures on the base changes of a polarised abelian surface with full level structure, i.e. the relative moduli problem underlying Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It is the form of representability used further on, where separatedness, quasi-compactness and local finite presentation of $\zeta$ are upgraded to finiteness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_represents_isSeparated_quasiCompact_locallyOfFinitePresentation_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_isSeparated_quasiCompact_locallyOfFinitePresentation_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (h2 : IsUnit (2 : R)) (X : PolarisedAbelianScheme 2 d m R) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
      (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
      IsSeparated ζ ∧ QuasiCompact ζ ∧ LocallyOfFinitePresentation ζ ∧

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'') := by sorry
