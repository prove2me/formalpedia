-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/2d94beca-41be-54e3-8a33-b8f18bdef8e6
-- title:
--   Algebraisation of a finite-over-P^r tower of fake elliptic curves
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule that is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, and let $star : \Lambda \to \Lambda$ satisfy $\mu \cdot star(x) = \bar x \mu$ for all $x \in \Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak m$-adic topology, $\mathfrak m$ its maximal ideal, and write $R_n = R/\mathfrak m^{n+1}$; let $\pi_n : R_{n+1} \to R_n$ be ring maps compatible with the quotient maps from $R$. Suppose given, for each $n$, a fake elliptic curve $E_n$ of level $1$ for $\Lambda$ over $R_n$ (a scheme $A_n \to \operatorname{Spec} R_n$ with commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, a $\Lambda$-action by group-law endomorphisms subject to the trace condition, and the level datum), together with morphisms $t_n : A_n \to A_{n+1}$ such that `IsPullbackVia` holds for $\pi_n$: each square identifies $A_n$ with the base change of $A_{n+1}$ along $\operatorname{Spec} \pi_n$, compatibly with the group laws, the $\Lambda$-actions, and lifting of points factoring through the level section. Suppose further given $r$ and morphisms $\iota_n : A_n \to \operatorname{Proj}$ of the homogeneous-polynomial grading on $R$ in $r+1$ variables, all finite, with $\iota_n$ followed by `ProjSpace.π R r` equal to $A_n \to \operatorname{Spec} R_n \to \operatorname{Spec} R$, and with $t_n$ followed by $\iota_{n+1}$ equal to $\iota_n$. Then there exist a level-$1$ fake elliptic curve $E_R$ for $\Lambda$ over $R$ and morphisms $j_n : A_n \to E_R.A$ such that each $j_n$ exhibits `IsPullbackVia` for the quotient map $R \to R_n$, and $t_n$ followed by $j_{n+1}$ equals $j_n$.
--
--   This is the Grothendieck existence (formal algebraisation) step for towers of fake elliptic curves: a compatible system over the truncations $R/\mathfrak m^{n+1}$, finite over projective space over $R$, comes from a single fake elliptic curve over the complete base. It is used in the Čerednik–Drinfeld part of the development to produce fake elliptic curves over complete local rings from their formal reduction towers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj.lean

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj
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
    (r : ℕ) (ι : ∀ n : ℕ, (E n).A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    (hι :
      (∀ n, IsFinite (ι n)) ∧
      (∀ n, ι n ≫ ProjSpace.π R r = (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ∧
      (∀ n, t n ≫ ι (n + 1) = ι n)) :
    ∃ (ER : FakeEllipticCurve Λ 1 R) (j : ∀ n : ℕ, (E n).A ⟶ ER.A),
      (∀ n, FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ER (E n) (j n)) ∧
      (∀ n, t n ≫ j (n + 1) = j n) := by sorry
