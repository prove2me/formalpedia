-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c6b49bbb-b4ba-576c-be08-6190ece417d7
-- title:
--   Line bundles on an algebraised tower of fake elliptic curves
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$ in the sense of the project predicate: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders under inclusion, let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}:\Lambda\to\Lambda$ satisfy $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $R$ be a noetherian local ring, complete for the adic topology of its maximal ideal $\mathfrak{m}$, write $R_n := R/\mathfrak{m}^{n+1}$, and let $\pi_n : R_{n+1}\to R_n$ be ring maps compatible with the quotient maps from $R$. Suppose given, for each $n$, a fake elliptic curve $E_n$ of level $1$ for $\Lambda$ over $R_n$ (an abelian scheme with commutative relative group law, two-dimensional fibres, a $\Lambda$-action subject to the trace condition, and the accompanying level datum), together with morphisms $t_n : (E_n).A \to (E_{n+1}).A$ which are pull-backs via $\pi_n$ in the project's sense: the square formed by $t_n$, the structure maps and $\mathrm{Spec}(\pi_n)$ is cartesian, $t_n$ carries the relative group law of $E_n$ to that of $E_{n+1}$ on points, it intertwines the two $\Lambda$-actions, and points of $E_n$ factoring through its level morphism push forward to points factoring through that of $E_{n+1}$. Suppose further given modules $\mathcal{L}_n$ on $(E_n).A$, each invertible in the sense that every point has an open neighbourhood on whose inclusion the pull-back of $\mathcal{L}_n$ is isomorphic to the unit module, with a nonempty set of isomorphisms $t_n^{*}\mathcal{L}_{n+1}\cong \mathcal{L}_n$ for each $n$. Finally suppose the tower is already algebraised: a fake elliptic curve $E_R$ of level $1$ for $\Lambda$ over $R$ and morphisms $j_n : (E_n).A \to E_R.A$ which are pull-backs, in the same sense, via the quotient maps $R\to R_n$, and which satisfy $t_n$ followed by $j_{n+1}$ equal to $j_n$. Then there is a module $\mathcal{M}$ on $E_R.A$, invertible in the above sense, such that for every $n$ the set of isomorphisms $j_n^{*}\mathcal{M}\cong \mathcal{L}_n$ is nonempty. No compatibility among these isomorphisms is asserted.
--
--   This is the line-bundle half of Grothendieck's existence (algebraisation) theorem in the form needed for towers of fake elliptic curves: once the tower of abelian schemes over the Artinian quotients $R/\mathfrak{m}^{n+1}$ has been algebraised over the complete local base $R$, a compatible system of invertible modules on the tower descends from a single invertible module on the algebraisation. It feeds the construction of fake elliptic curves over $R$ out of formal towers, being used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fakeEllipticCurve_forall_isPullbackVia_of_tower_of_finiteBySections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_forall_pullback_iso_of_tower_of_isPullbackVia
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
    (ER : FakeEllipticCurve Λ 1 R) (j : ∀ n : ℕ, (E n).A ⟶ ER.A)
    (hj : ∀ n, FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ER (E n) (j n))
    (hjt : ∀ n, t n ≫ j (n + 1) = j n) :
    ∃ 𝓜 : ER.A.Modules, Scheme.Modules.IsInvertible 𝓜 ∧
      ∀ n, Nonempty ((Scheme.Modules.pullback (j n)).obj 𝓜 ≅ 𝓛 n) := by sorry
