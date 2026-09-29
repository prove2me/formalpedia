-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7093ecbc-7fc6-5ea9-997f-d8b6c334065a
-- title:
--   Scheme-level algebraisation of a tower finite over P^r_R
-- statement:
--   Let $q \neq q'$ be primes and let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0 < a$ or $0 < b$, and for a finite place $v$ of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ lies over $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order: containing $1$, closed under multiplication, with $\mathbb{Q}$-span everything and finitely generated; maximal among such), let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, and let $\operatorname{star} \colon \Lambda \to \Lambda$ satisfy $\mu \cdot \operatorname{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, $\mathfrak{m}$ its maximal ideal, and for each $n$ let $\pi_n \colon R/\mathfrak{m}^{n+2} \to R/\mathfrak{m}^{n+1}$ be a ring homomorphism compatible with the quotient maps from $R$. Let $E_n$ be a fake elliptic curve of level $1$ with $\Lambda$-action over $R/\mathfrak{m}^{n+1}$ (an abelian scheme $(E_n).f \colon (E_n).A \to \operatorname{Spec}(R/\mathfrak{m}^{n+1})$ with commutative relative group law, smooth proper with connected fibres, fibres of dimension $2$, an action of $\Lambda$ and a level datum), and let $t_n \colon (E_n).A \to (E_{n+1}).A$ satisfy `IsPullbackVia` $\pi_n$: the square formed by $t_n$, $(E_n).f$, $(E_{n+1}).f$ and $\operatorname{Spec}(\pi_n)$ is a pullback, $t_n$ respects the relative group laws and the $\Lambda$-actions, and points factoring through the level morphism of $E_n$ are carried to points factoring through that of $E_{n+1}$. Finally let $r \in \mathbb{N}$ and, writing $\mathbb{P}^r_R = \operatorname{Proj}$ of the homogeneous subalgebra of $R[x_0,\dots,x_r]$, let $\iota_n \colon (E_n).A \to \mathbb{P}^r_R$ be morphisms such that each $\iota_n$ is finite, each $\iota_n$ followed by the structural morphism `ProjSpace.π R r` equals $(E_n).f$ followed by $\operatorname{Spec}$ of the quotient map $R \to R/\mathfrak{m}^{n+1}$, and $t_n$ followed by $\iota_{n+1}$ equals $\iota_n$. Then there exist a scheme $Z$, a finite morphism $G \colon Z \to \mathbb{P}^r_R$ and morphisms $j_n \colon (E_n).A \to Z$ such that $j_n$ followed by $G$ is $\iota_n$, $t_n$ followed by $j_{n+1}$ is $j_n$, and for every $n$ the square formed by $j_n$, $(E_n).f$, $G$ followed by `ProjSpace.π R r`, and $\operatorname{Spec}$ of $R \to R/\mathfrak{m}^{n+1}$ is a pullback.
--
--   This is the scheme-theoretic half of the algebraisation step for towers of fake elliptic curves: Grothendieck's existence theorem, in the form for compatible systems of schemes finite over the truncations of $\mathbb{P}^r_R$, produces a single $R$-scheme $Z$, finite over $\mathbb{P}^r_R$, whose base changes to the $R/\mathfrak{m}^{n+1}$ recover the given tower. The conclusion records only the scheme $Z$ with its pullback squares; the group law, the $\Lambda$-action and the level datum are transported to $Z$ in the companion statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_isFinite_proj), which cites this result.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_forall_isPullback_of_tower_of_isFinite_proj
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
    ∃ (Z : Scheme.{0}) (G : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) (_ : IsFinite G) (jz : ∀ n : ℕ, (E n).A ⟶ Z),
      (∀ n, jz n ≫ G = ι n) ∧
      (∀ n, t n ≫ jz (n + 1) = jz n) ∧
      (∀ n, CategoryTheory.IsPullback (jz n) (E n).f (G ≫ ProjSpace.π R r) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))) := by sorry
