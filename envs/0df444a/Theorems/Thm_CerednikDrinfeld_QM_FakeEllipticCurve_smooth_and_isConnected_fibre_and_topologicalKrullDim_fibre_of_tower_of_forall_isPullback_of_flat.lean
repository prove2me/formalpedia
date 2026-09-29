-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smooth_and_isConnected_fibre_and_topologicalKrullDim_fibre_of_tower_of_forall_isPullback_of_flat
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.smooth_and_isConnected_fibre_and_topologicalKrullDim_fibre_of_tower_of_forall_isPullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/e93a35b0-479e-58c3-a744-03611326fbf4
-- title:
--   Smooth proper fibres of dimension two for an algebraised tower
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a, b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order: containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning and finitely generated; maximal among orders containing it), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, and let $\operatorname{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \operatorname{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $R$ be a noetherian local ring, complete for the adic topology of its maximal ideal $\mathfrak{m}$, equipped with ring maps $\pi_n : R/\mathfrak{m}^{n+2} \to R/\mathfrak{m}^{n+1}$ compatible with the quotient maps. Let $E_n$ be a fake elliptic curve for $\Lambda$ of level $1$ over $R/\mathfrak{m}^{n+1}$ (in the project's sense: a scheme $A_n$ smooth and proper over $\operatorname{Spec}(R/\mathfrak{m}^{n+1})$ with connected fibres of topological Krull dimension $2$, a commutative relative group law, a $\Lambda$-action with the prescribed trace condition, and level data), and let $t_n : A_n \to A_{n+1}$ exhibit $E_n$ as the base change of $E_{n+1}$ along $\pi_n$, compatibly with the group laws, the $\Lambda$-actions and the level structures. Let $r \in \mathbb{N}$, let $Z$ be a scheme with a finite morphism $G$ to $\mathrm{Proj}$ of the graded ring of homogeneous polynomials in $r+1$ variables over $R$, and let $j_n : A_n \to Z$ satisfy $t_n$ followed by $j_{n+1}$ equals $j_n$ and make each square with $j_n$, $A_n \to \operatorname{Spec}(R/\mathfrak{m}^{n+1})$, the composite $f_Z$ of $G$ with `ProjSpace.π R r`, and $\operatorname{Spec}$ of the quotient map $R \to R/\mathfrak{m}^{n+1}$ cartesian. Assume $f_Z$ is flat. Then $f_Z$ is smooth and proper, and for every point $s$ of $\operatorname{Spec} R$ the fibre $f_Z^{-1}(s)$ is connected and has topological Krull dimension $2$.
--
--   This records the geometric properties of the scheme $Z$ that algebraises a tower of fake elliptic curves over the artinian quotients $R/\mathfrak{m}^{n+1}$ of a complete local noetherian ring: properness comes from finiteness over projective space, and smoothness together with connectedness and dimension $2$ of all fibres is propagated from the closed fibre $A_0$ by flatness and properness. It feeds the construction of a fake elliptic curve over $R$ itself pulling back to the given tower, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_forall_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smooth_and_isConnected_fibre_and_topologicalKrullDim_fibre_of_tower_of_forall_isPullback_of_flat.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.smooth_and_isConnected_fibre_and_topologicalKrullDim_fibre_of_tower_of_forall_isPullback_of_flat
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

    (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))
    {r : ℕ}
    (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsFinite G] (jz : ∀ n : ℕ, (E n).A ⟶ Z)
    (hZ :
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))))
    (hflat : Flat (G ≫ ProjSpace.π R r)) :
    Smooth (G ≫ ProjSpace.π R r) ∧ IsProper (G ≫ ProjSpace.π R r) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), _root_.IsConnected ((G ≫ ProjSpace.π R r).base ⁻¹' {s})) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), topologicalKrullDim ↥((G ≫ ProjSpace.π R r).base ⁻¹' {s}) = 2) := by sorry
