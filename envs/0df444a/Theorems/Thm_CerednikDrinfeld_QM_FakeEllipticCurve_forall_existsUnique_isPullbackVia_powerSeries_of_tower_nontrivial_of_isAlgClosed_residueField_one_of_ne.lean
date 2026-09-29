-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/dfb2de6a-877d-5389-ad5f-778a01ab535c
-- title:
--   Versality of a non-trivial tower over O[[t]]
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $a>0$ or $b>0$ and, for a height-one prime $v$ of the integers of $\mathbb Q$, every nonzero element of the $v$-adic completion of the algebra is a unit exactly when $v$ lies over $q$ or $q'$; let $\Lambda$ be a maximal order (an order maximal among orders), and $p$ a prime with $p\neq q,q'$. Let $O$ be a Noetherian local domain, a discrete valuation ring, complete for the maximal-ideal-adic topology, with algebraically closed residue field, in which $p$ is a nonzero element of the maximal ideal. Write $R_n=\mathrm{PowerSeries}\,O/\mathfrak m^{n+1}$. The data are: a fake elliptic curve $E_0$ of level $1$ over the residue field $k$ of $O$ (in the sense of the structure `FakeEllipticCurve`: a scheme over the base with a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action satisfying the trace condition, and a level datum); a bijective ring homomorphism $\iota_0\colon R_0\to k$ compatible with the residue map of $O$; reduction maps $\pi_n\colon R_{n+1}\to R_n$ compatible with the quotient maps; fake elliptic curves $E_n$ of level $1$ over $R_n$ together with morphisms $t_n\colon (E_n).A\to (E_{n+1}).A$ exhibiting $E_{n+1}$ as a pullback of $E_n$ along $\pi_n$ in the sense of `IsPullbackVia` (cartesian square, compatibility with the group laws, $\Lambda$-equivariance, and the level condition); composites $\mathrm{tchain}_n\colon (E_0).A\to (E_n).A$ with $\mathrm{tchain}_0=\mathrm{id}$ and $\mathrm{tchain}_{n+1}=\mathrm{tchain}_n$ followed by $t_n$; a morphism $g_0\colon E_0.A\to (E_0).A$ making $E_0$ the pullback of the bottom curve along $\iota_0$. Assume first-order non-triviality: for every ring homomorphism $\tau\colon R_1\to k[\varepsilon]$ that is $O$-compatible and sends the class of $X$ to $\varepsilon$, every fake elliptic curve $w$ over $k[\varepsilon]$ with a morphism $hw$ exhibiting $w$ as the pullback of $E_1$ along $\tau$, and every $gw\colon E_0.A\to w.A$ exhibiting $E_0$ as the pullback of $w$ along the projection $k[\varepsilon]\to k$ with $gw$ followed by $hw$ equal to $g_0$ followed by $\mathrm{tchain}_1$, there is no $h\colon w.A\to E_0.A$ which is a pullback along $k\to k[\varepsilon]$ with $gw$ followed by $h$ the identity. The conclusion: for every Artin local commutative $O$-algebra $B$, every surjective $\rho\colon B\to k$ with $\rho$ composed after the structure map equal to the residue map of $O$, every fake elliptic curve $E'$ of level $1$ over $B$ and every $g'\colon E_0.A\to E'.A$ exhibiting $E_0$ as the pullback of $E'$ along $\rho$, and every $n$ with $\mathfrak m_B^{n+1}=0$, there exist a ring homomorphism $\varphi\colon R_n\to B$ with $\rho\circ\varphi=\iota_0$ composed with the canonical map $R_n\to R_0$ and with $\varphi$ compatible with the $O$-algebra structures, and a morphism $h\colon E'.A\to (E_n).A$ exhibiting $E'$ as the pullback of $E_n$ along $\varphi$, such that $g'$ followed by $h$ equals $g_0$ followed by $\mathrm{tchain}_n$; and any $\varphi',h'$ with these same three properties coincide with $\varphi$ and $h$.
--
--   This is the versality and uniqueness statement for the Čerednik–Drinfeld deformation theory of fake elliptic curves of level $1$: a tower over $O[[t]]$ whose first-order member is a non-trivial deformation of $E_0$ pro-represents the deformation functor on Artin local $O$-algebras, in the manner of Schlessinger's criterion. It is the block used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne), which combines it with the existence of such a tower to produce a regular versal deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne.lean

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
open IsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_existsUnique_isPullbackVia_powerSeries_of_tower_nontrivial_of_isAlgClosed_residueField_one_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q')
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed (ResidueField O)]
    (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0)
    (E₀ : FakeEllipticCurve Λ 1 (ResidueField O))

    (ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
    (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O)
    (π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)))
    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

    (tchain : ∀ n : ℕ, (E 0).A ⟶ (E n).A) (htchain₀ : tchain 0 = 𝟙 _)
    (htchain : ∀ n, tchain (n + 1) = tchain n ≫ t n)
    (g₀ : E₀.A ⟶ (E 0).A) (hg₀ : FakeEllipticCurve.IsPullbackVia ι₀ (E 0) E₀ g₀)

    (hnt : ∀ (τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O))
      (_ : τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
        (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O))
      (_ : τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps)
      (w : FakeEllipticCurve Λ 1 (DualNumber (ResidueField O))) (hw : w.A ⟶ (E 1).A)
      (_ : FakeEllipticCurve.IsPullbackVia τ (E 1) w hw)
      (gw : E₀.A ⟶ w.A)
      (_ : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom w E₀ gw)
      (_ : gw ≫ hw = g₀ ≫ tchain 1),
      ¬ ∃ h : w.A ⟶ E₀.A,
        FakeEllipticCurve.IsPullbackVia (algebraMap (ResidueField O) (DualNumber (ResidueField O))) E₀ w h ∧ gw ≫ h = 𝟙 E₀.A) :

      ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (ρ : B →+* ResidueField O) (hρ : Function.Surjective ρ) (hρO : ρ.comp (algebraMap O B) = residue O)
        (E' : FakeEllipticCurve Λ 1 B) (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g'),
        ∀ (n : ℕ), maximalIdeal B ^ (n + 1) = ⊥ →
        ∃ (φ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)) →+* B)
          (hφ : ρ.comp φ = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
          (hφO : φ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1))).comp (algebraMap O (PowerSeries O))) = algebraMap O B)
          (h : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ (E n) E' h ∧ g' ≫ h = g₀ ≫ tchain n ∧

          ∀ (φ' : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)) →+* B)
            (_ : ρ.comp φ' = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
            (_ : φ'.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1))).comp (algebraMap O (PowerSeries O))) = algebraMap O B)
            (h' : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ' (E n) E' h' → g' ≫ h' = g₀ ≫ tchain n →
            φ' = φ ∧ h' = h := by sorry
