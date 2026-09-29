-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/20d11e1f-2438-57bb-bfe4-8fcba597f24b
-- title:
--   Versal deformation tower for fake elliptic curves away from qq'
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for a height-one prime $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) exactly when $v$ lies over $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order, i.e. an order maximal among orders. Let $p$ be a prime with $p \neq q$, $p \neq q'$, let $\bar k$ be an algebraically closed field of characteristic $p$, and let $E_0$ be a fake elliptic curve of level $1$ over $\bar k$ in the sense of `FakeEllipticCurve` (an abelian scheme over $\mathrm{Spec}\,\bar k$ with commutative relative group law, all fibres of dimension $2$, an action of $\Lambda$ compatible with the group law and satisfying the trace condition, together with the level datum). Then there is a ring $R$, regular local and regular, of Krull dimension at most $2$, complete for the $\mathfrak m$-adic topology on its maximal ideal $\mathfrak m$, with $p \neq 0$ in $R$, carrying: a ring isomorphism $\iota_0 : R/\mathfrak m \to \bar k$ (a bijective ring homomorphism); surjections $\pi_n : R/\mathfrak m^{n+2} \to R/\mathfrak m^{n+1}$ compatible with the quotient maps from $R$; fake elliptic curves $E_n$ of level $1$ over $R/\mathfrak m^{n+1}$; and morphisms $t_n : (E_n).A \to (E_{n+1}).A$ with `IsPullbackVia` $\pi_n$, that is, each square exhibiting $E_n$ as the base change of $E_{n+1}$ along $\pi_n$, compatibly with the group laws, with the $\Lambda$-actions, and with lifting of level sections. There are further the composites $\mathrm{tchain}_n : (E_0).A \to (E_n).A$ determined by $\mathrm{tchain}_0 = \mathrm{id}$ and $\mathrm{tchain}_{n+1} = \mathrm{tchain}_n$ followed by $t_n$, and a morphism $g_0 : E_0.A \to (E_0\text{-stage}).A$ exhibiting the given $E_0$ as the base change of the bottom stage along $\iota_0$ in the same sense. This tower is versal with a unique lift: for every Artinian local ring $B$ and every surjection $\rho : B \to \bar k$ with kernel the maximal ideal of $B$, every fake elliptic curve $E'$ of level $1$ over $B$ and every $g'$ exhibiting $E_0$ as the base change of $E'$ along $\rho$, and every $n$ with $\mathfrak m_B^{n+1} = 0$, there exist a ring homomorphism $\varphi : R/\mathfrak m^{n+1} \to B$ with $\rho \circ \varphi$ equal to $\iota_0$ composed with the reduction $R/\mathfrak m^{n+1} \to R/\mathfrak m$, and a morphism $h : E'.A \to (E_n).A$ exhibiting $E'$ as the base change of $E_n$ along $\varphi$, such that $g'$ followed by $h$ equals $g_0$ followed by $\mathrm{tchain}_n$; and the pair $(\varphi, h)$ is the only one with these properties.
--
--   This is the Serre–Tate style statement that the deformation functor of a fake elliptic curve of level $1$ over an algebraically closed field of characteristic $p$, for $p$ prime to the discriminant $qq'$ of the indefinite quaternion algebra, admits a regular complete local hull of Krull dimension at most $2$, presented concretely as an algebraised tower of curves over the truncations $R/\mathfrak m^{n+1}$ together with a rigid (uniquely liftable) versality property. It is the characteristic-$p$, away-from-the-discriminant input to the construction of integral models with good reduction for the associated Shimura curve, and is used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q')
    (kbar : Type) [Field kbar] [IsAlgClosed kbar] [CharP kbar p]
    (E₀ : FakeEllipticCurve Λ 1 kbar) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsRegularRing R) (hdim : ringKrullDim R ≤ 2)
      (_ : IsAdicComplete (maximalIdeal R) R)
      (hp : ((p : ℕ) : R) ≠ 0)
      (ι₀ : (R ⧸ maximalIdeal R ^ (0 + 1)) →+* kbar) (hι₀ : Function.Bijective ι₀)
      (π : ∀ n : ℕ, (R ⧸ maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ maximalIdeal R ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
      (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ maximalIdeal R ^ (n + 1)))
      (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
      (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

      (tchain : ∀ n : ℕ, (E 0).A ⟶ (E n).A) (htchain₀ : tchain 0 = 𝟙 _)
      (htchain : ∀ n, tchain (n + 1) = tchain n ≫ t n)
      (g₀ : E₀.A ⟶ (E 0).A) (hg₀ : FakeEllipticCurve.IsPullbackVia ι₀ (E 0) E₀ g₀),

      ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
        (ρ : B →+* kbar) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = maximalIdeal B)
        (E' : FakeEllipticCurve Λ 1 B) (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g'),
        ∀ (n : ℕ), maximalIdeal B ^ (n + 1) = ⊥ →
        ∃ (φ : (R ⧸ maximalIdeal R ^ (n + 1)) →+* B)
          (hφ : ρ.comp φ = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
          (h : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ (E n) E' h ∧ g' ≫ h = g₀ ≫ tchain n ∧

          ∀ (φ' : (R ⧸ maximalIdeal R ^ (n + 1)) →+* B)
            (_ : ρ.comp φ' = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
            (h' : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ' (E n) E' h' → g' ≫ h' = g₀ ≫ tchain n →
            φ' = φ ∧ h' = h := by sorry
