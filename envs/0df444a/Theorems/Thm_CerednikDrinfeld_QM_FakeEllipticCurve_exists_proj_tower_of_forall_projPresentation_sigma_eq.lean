-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_proj_tower_of_forall_projPresentation_sigma_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_proj_tower_of_forall_projPresentation_sigma_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/cc19feaf-57c7-5c3d-9666-388ef03d3408
-- title:
--   Compatible P^r_R-presentations along a tower of fake elliptic curves
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a maximal order (an order, in the sense of containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$ and finitely generated, maximal among such), let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$. Let $R$ be a Noetherian local ring, complete for the $\mathfrak{m}$-adic topology, write $R_n = R/\mathfrak{m}^{n+1}$, and let $\pi_n : R_{n+1} \to R_n$ be ring maps with $\pi_n \circ (\text{quotient map of } \mathfrak{m}^{n+2}) = (\text{quotient map of } \mathfrak{m}^{n+1})$. Let $E_n$ be a fake elliptic curve over $R_n$ with $\Lambda$-action and level datum $N = 1$, and $t_n : (E_n).A \to (E_{n+1}).A$ witnesses of `IsPullbackVia` $\pi_n$: the square formed by $t_n$, the two structure morphisms and $\mathrm{Spec}(\pi_n)$ is cartesian, $t_n$ carries the relative group law of $E_n$ to that of $E_{n+1}$, intertwines the $\Lambda$-actions, and carries points factoring through $(E_n).\mathrm{lev}$ to points factoring through $(E_{n+1}).\mathrm{lev}$. Let $\mathcal{M}_n$ be $\mathcal{O}_{(E_n).A}$-modules with isomorphisms $e_n : t_n^{*}\mathcal{M}_{n+1} \cong \mathcal{M}_n$, and for a fixed $r$ let $\mathfrak{P}_n$ be a `ProjPresentation` of $\mathcal{M}_n$ over the composite $(E_n).f$ followed by $\mathrm{Spec}(R \to R_n)$ of degree $r$: that is, $r+1$ global sections $\sigma_i$ of $\mathcal{M}_n$, a morphism $\mathfrak{P}_n.\mathrm{toProj}$ to $\mathrm{Proj}$ of the homogeneous polynomials in $r+1$ variables over $R$ lying over that composite, such that on any open contained in the preimage of the basic open $D(X_i)$ multiplication by the restriction of $\sigma_i$ is bijective, and the pullback of the ratio $X_j/X_i$ sends $\sigma_i$ to $\sigma_j$. Assume the sections are compatible: $(\mathfrak{P}_n).\sigma_i = e_n\big(t_n^{*}(\mathfrak{P}_{n+1}).\sigma_i\big)$ for all $n$ and $i$, where $t_n^{*}$ is the unit of the pullback–pushforward adjunction evaluated at $\top$. Then there is a family of morphisms $\iota_n : (E_n).A \to \mathbb{P}^r_R$ with $\iota_n = (\mathfrak{P}_n).\mathrm{toProj}$, with $\iota_n$ followed by the structure morphism of $\mathbb{P}^r_R$ equal to $(E_n).f$ followed by $\mathrm{Spec}(R \to R_n)$, and with $t_n$ followed by $\iota_{n+1}$ equal to $\iota_n$ for every $n$. The proof uses only the cartesian square contained in the `IsPullbackVia` hypotheses, the compatibility of the maps $\pi_n$ with the quotient maps, and the compatibility of the sections; the hypotheses on the quaternion algebra, the order $\Lambda$, the element $\mu$ and the map $\mathrm{star}$.
--
--   This is the gluing step that turns a compatible family of sections-presentations on a formal tower of fake elliptic curves into a single compatible tower of morphisms into one projective space $\mathbb{P}^r_R$ over the complete base, the scheme-theoretic form of the classical statement that $r+1$ generating global sections of a line bundle determine a morphism to $\mathbb{P}^r$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_proj_tower_of_forall_projPresentation_sigma_eq.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_proj_tower_of_forall_projPresentation_sigma_eq
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

    (𝓜 : ∀ n : ℕ, (E n).A.Modules)
    (e𝓜 : ∀ n, (Scheme.Modules.pullback (t n)).obj (𝓜 (n + 1)) ≅ 𝓜 n)
    (r : ℕ)
    (𝔓 : ∀ n : ℕ, Scheme.Modules.ProjPresentation (𝓜 n)
      ((E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) r)
    (hσ : ∀ (n : ℕ) (i : Fin (r + 1)), (𝔓 n).σ i =
      ((e𝓜 n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction (t n)).unit.app (𝓜 (n + 1))).app ⊤) ((𝔓 (n + 1)).σ i))) :
    ∃ ι : ∀ n : ℕ, (E n).A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R),
      (∀ n, ι n = (𝔓 n).toProj) ∧
      (∀ n, ι n ≫ ProjSpace.π R r = (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ∧
      (∀ n, t n ≫ ι (n + 1) = ι n) := by sorry
