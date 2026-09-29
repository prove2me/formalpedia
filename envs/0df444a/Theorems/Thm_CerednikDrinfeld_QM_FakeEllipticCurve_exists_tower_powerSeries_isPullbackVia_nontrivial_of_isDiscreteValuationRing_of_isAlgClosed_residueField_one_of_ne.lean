-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tower_powerSeries_isPullbackVia_nontrivial_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tower_powerSeries_isPullbackVia_nontrivial_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ea1a1da4-93a1-564e-aa0d-bd2aaae12d74
-- title:
--   Non-trivial formal tower of fake elliptic curves over O[[t]]
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb Q$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb Q$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$; let $\Lambda$ be a maximal order (an order maximal among the orders containing it), and $p$ a prime distinct from $q$ and $q'$. Let $O$ be a noetherian local domain, complete for the maximal-adic topology, a discrete valuation ring with algebraically closed residue field $k=$ `ResidueField O`, with $p\in\mathfrak m_O$ and $p\neq 0$ in $O$, and let $E_0$ be a fake elliptic curve of level $1$ over $k$ (an abelian-scheme bundle over $\operatorname{Spec}k$ with commutative relative group law, two-dimensional fibres, $\Lambda$-action with the prescribed trace conditions, and level datum). Write $R_n=$ `PowerSeries O`$/\mathfrak m^{\,n+1}$. The assertion is the existence of: a bijective ring map $\iota_0\colon R_0\to k$ compatible with $O\to R_0$ and the residue map; reduction maps $\pi_n\colon R_{n+1}\to R_n$ commuting with the quotient maps; fake elliptic curves $E_{(n)}$ of level $1$ over $R_n$; morphisms $t_n\colon E_{(n)}.A\to E_{(n+1)}.A$ exhibiting $E_{(n)}$ as the pullback of $E_{(n+1)}$ along $\pi_n$ in the sense of `IsPullbackVia` (cartesian square over $\operatorname{Spec}\pi_n$, compatible with the group laws, the $\Lambda$-actions and the level data); composites $\mathrm{tchain}_n\colon E_{(0)}.A\to E_{(n)}.A$ with $\mathrm{tchain}_0=\mathrm{id}$ and $\mathrm{tchain}_{n+1}=\mathrm{tchain}_n$ followed by $t_n$; and $g_0\colon E_0.A\to E_{(0)}.A$ exhibiting $E_0$ as the pullback of $E_{(0)}$ along $\iota_0$; such that, moreover, the first-order term is non-trivial: for every ring map $\tau\colon R_1\to k[\varepsilon]$ which is compatible with $O$ via the residue map and sends the class of $X$ to $\varepsilon$, every fake elliptic curve $w$ over $k[\varepsilon]$ with $hw\colon w.A\to E_{(1)}.A$ cartesian over $\tau$, and every $gw\colon E_0.A\to w.A$ cartesian over the projection $k[\varepsilon]\to k$ with $gw$ followed by $hw$ equal to $g_0$ followed by $\mathrm{tchain}_1$, there is no $h\colon w.A\to E_0.A$ exhibiting $w$ as the base change of $E_0$ along $k\to k[\varepsilon]$ with $gw$ followed by $h$ the identity of $E_0.A$.
--
--   This is the deformation-theoretic input producing, over the truncations of $O[[t]]$, a formal family of level-one fake elliptic curves lifting a given curve over the algebraically closed residue field, whose first-order part along $t$ is a non-trivial deformation over the dual numbers; it rests on unobstructedness of lifting along small surjections of Artin local rings together with the description of the one-dimensional tangent space. It is used in the construction of the versal formal tower over a regular base for these curves, in the Čerednik–Drinfeld uniformisation package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tower_powerSeries_isPullbackVia_nontrivial_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tower_powerSeries_isPullbackVia_nontrivial_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q')
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed (ResidueField O)]
    (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0)
    (E₀ : FakeEllipticCurve Λ 1 (ResidueField O)) :
    ∃ (ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
      (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O)
      (π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)))
      (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
      (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
      (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

      (tchain : ∀ n : ℕ, (E 0).A ⟶ (E n).A) (htchain₀ : tchain 0 = 𝟙 _)
      (htchain : ∀ n, tchain (n + 1) = tchain n ≫ t n)
      (g₀ : E₀.A ⟶ (E 0).A) (hg₀ : FakeEllipticCurve.IsPullbackVia ι₀ (E 0) E₀ g₀),

      ∀ (τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O))
        (_ : τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
          (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O))
        (_ : τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps)
        (w : FakeEllipticCurve Λ 1 (DualNumber (ResidueField O))) (hw : w.A ⟶ (E 1).A)
        (_ : FakeEllipticCurve.IsPullbackVia τ (E 1) w hw)
        (gw : E₀.A ⟶ w.A)
        (_ : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom w E₀ gw)
        (_ : gw ≫ hw = g₀ ≫ tchain 1),
        ¬ ∃ h : w.A ⟶ E₀.A,
          FakeEllipticCurve.IsPullbackVia (algebraMap (ResidueField O) (DualNumber (ResidueField O))) E₀ w h ∧ gw ≫ h = 𝟙 E₀.A := by sorry
