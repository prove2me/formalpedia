-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_tower_of_finiteBySections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/20a1aa09-8498-5ccb-a41f-f980d2b7ab14
-- title:
--   Finite maps to one P^r_R along a formal tower
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ with $\mathbb{H}[\mathbb{Q},a,b]$ indefinite ($0 < a$ or $0 < b$) and ramified exactly at $q,q'$, in the sense that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra precisely when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such), let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$. Let $R$ be a noetherian local ring, complete for the $\mathfrak{m}$-adic topology, write $R_n = R/\mathfrak{m}^{n+1}$, and let $\pi_n : R_{n+1} \to R_n$ be ring maps commuting with the quotient maps from $R$. Let $E_n$ be a fake elliptic curve for $\Lambda$ of level $1$ over $R_n$ and $t_n : (E_n).A \to (E_{n+1}).A$ morphisms such that each `IsPullbackVia` holds: $t_n$ makes $(E_n).A$ the fibre product of $(E_{n+1}).A$ with $\operatorname{Spec} R_n$ over $\operatorname{Spec} R_{n+1}$, is compatible with the relative group laws, commutes with the $\Lambda$-actions, and carries points factoring through the level scheme of $E_n$ to points factoring through that of $E_{n+1}$. Let $\mathcal{L}_n$ be modules on $(E_n).A$, each invertible (locally isomorphic to the unit module), with $t_n^{*}\mathcal{L}_{n+1} \cong \mathcal{L}_n$, and suppose $\mathcal{L}_0 \otimes \mathcal{L}_0 \otimes \mathcal{L}_0$ is finite by sections over $(E_0).f$, i.e. admits a `ProjPresentation` of some size $N$ relative to $(E_0).f$ whose associated morphism to $\operatorname{Proj}$ of the polynomial ring in $N+1$ variables is finite. Then there are $r \in \mathbb{N}$ and morphisms $\iota_n : (E_n).A \to \mathbb{P}^r_R = \operatorname{Proj}$ of the degree grading on $R[x_0,\dots,x_r]$ such that every $\iota_n$ is finite, $\iota_n$ followed by the structure projection $\mathbb{P}^r_R \to \operatorname{Spec} R$ equals $(E_n).f$ followed by $\operatorname{Spec}$ of the quotient map $R \to R_n$, and $t_n$ followed by $\iota_{n+1}$ equals $\iota_n$ for all $n$.
--
--   This is the projective-embedding half of Grothendieck's formal existence theorem (EGA III 5.4.5) in the setting of fake elliptic curves: an ample cube on the special fibre is propagated along the tower of nilpotent thickenings to a single family of finite morphisms into one fixed projective space over the complete base $R$. It is the geometric input for the algebraisation step producing a fake elliptic curve over $R$ itself, cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_tower_of_finiteBySections.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections
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

    (𝓛 : ∀ n : ℕ, (E n).A.Modules)
    (hinv : ∀ n, Scheme.Modules.IsInvertible (𝓛 n))
    (hcompat : ∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n))
    (hample : Scheme.Modules.FiniteBySections ((𝓛 0) ⊗ (𝓛 0) ⊗ (𝓛 0)) (E 0).f) :
    ∃ (r : ℕ) (ι : ∀ n : ℕ, (E n).A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)),
      (∀ n, IsFinite (ι n)) ∧
      (∀ n, ι n ≫ ProjSpace.π R r = (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ∧
      (∀ n, t n ≫ ι (n + 1) = ι n) := by sorry
