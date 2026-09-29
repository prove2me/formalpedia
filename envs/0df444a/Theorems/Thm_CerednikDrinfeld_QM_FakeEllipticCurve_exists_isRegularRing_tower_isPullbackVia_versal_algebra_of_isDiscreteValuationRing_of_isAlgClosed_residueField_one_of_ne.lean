-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/adb9ba8e-e63e-5b28-8a38-45c33479e58d
-- title:
--   Versal deformation tower of a level-one fake elliptic curve
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders for inclusion, and let $p$ be a prime with $p\neq q$, $p\neq q'$. Let $O$ be a Noetherian local domain which is a discrete valuation ring, complete for the $\mathfrak{m}_O$-adic topology, with algebraically closed residue field, and with $p\in\mathfrak{m}_O$, $p\neq 0$ in $O$; let $E_0$ be a fake elliptic curve of level $1$ over $\mathrm{ResidueField}\,O$, i.e. a scheme over the residue field with a commutative relative group law, the abelian-scheme property bundle, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base additive and multiplicative in $\Lambda$ and satisfying the trace condition, together with the level datum. Then there is a commutative ring $R$ which is a regular local ring, regular, of Krull dimension at most $2$, complete for the $\mathfrak{m}_R$-adic topology, an $O$-algebra with $p\neq 0$ in $R$, together with: a bijective ring homomorphism $\iota_0\colon R/\mathfrak{m}_R\to \mathrm{ResidueField}\,O$ whose composite with $O\to R/\mathfrak{m}_R$ is the residue map of $O$; truncations $\pi_n\colon R/\mathfrak{m}_R^{n+2}\to R/\mathfrak{m}_R^{n+1}$ compatible with the quotient maps; fake elliptic curves $E_n$ of level $1$ over $R/\mathfrak{m}_R^{n+1}$; morphisms $t_n\colon E_n.A\to E_{n+1}.A$ exhibiting $E_n$ as the pullback of $E_{n+1}$ along $\pi_n$ in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square over $\mathrm{Spec}$ of the ring map, compatibility with the relative group laws and with the $\Lambda$-actions, and factorisation of level-structure points); composites $\mathrm{tchain}_n\colon E_0.A\to E_n.A$ with $\mathrm{tchain}_0=\mathrm{id}$ and $\mathrm{tchain}_{n+1}=\mathrm{tchain}_n$ followed by $t_n$; and $g_0\colon E_0.A\to E_{(0)}.A$ exhibiting $E_0$ as the pullback of $E_{(0)}$ along $\iota_0$. This tower is versal in the following sense: for every Artinian local $O$-algebra $B$ with a surjective ring homomorphism $\rho\colon B\to\mathrm{ResidueField}\,O$ whose composite with $O\to B$ is the residue map of $O$, every fake elliptic curve $E'$ of level $1$ over $B$ and every $g'\colon E_0.A\to E'.A$ exhibiting $E_0$ as the pullback of $E'$ along $\rho$, and every $n$ with $\mathfrak{m}_B^{n+1}=0$, there are a ring homomorphism $\varphi\colon R/\mathfrak{m}_R^{n+1}\to B$ with $\rho\circ\varphi$ equal to $\iota_0$ precomposed with the canonical map $R/\mathfrak{m}_R^{n+1}\to R/\mathfrak{m}_R$ and with $\varphi$ compatible with the structural maps from $O$, and a morphism $h\colon E'.A\to E_n.A$ exhibiting $E'$ as the pullback of $E_n$ along $\varphi$ with $g'$ followed by $h$ equal to $g_0$ followed by $\mathrm{tchain}_n$; and any pair $(\varphi',h')$ with the same three properties satisfies $\varphi'=\varphi$ and $h'=h$.
--
--   This is the Serre–Tate style deformation statement for fake elliptic curves of level $1$ over a complete discrete valuation ring with algebraically closed residue field, in the case of a residue characteristic $p$ distinct from both ramified primes $q,q'$ of the quaternion algebra: a two-dimensional complete regular local hull carrying a tower of truncated deformations that is versal with unique liftings at each finite level. It feeds the Čerednik–Drinfeld analysis of the Shimura curve attached to $\Lambda$, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_ringKrullDim_le_two_tower_isPullbackVia_versal_one_of_isAlgClosed_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isRegularRing_tower_isPullbackVia_versal_algebra_of_isDiscreteValuationRing_of_isAlgClosed_residueField_one_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q')
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed (ResidueField O)]
    (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0)
    (E₀ : FakeEllipticCurve Λ 1 (ResidueField O)) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsRegularRing R) (hdim : ringKrullDim R ≤ 2) (_ : IsAdicComplete (maximalIdeal R) R)
      (_ : Algebra O R)
      (hp : ((p : ℕ) : R) ≠ 0)
      (ι₀ : (R ⧸ maximalIdeal R ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
      (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))).comp (algebraMap O R)) = residue O)
      (π : ∀ n : ℕ, (R ⧸ maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ maximalIdeal R ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
      (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ maximalIdeal R ^ (n + 1)))
      (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
      (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

      (tchain : ∀ n : ℕ, (E 0).A ⟶ (E n).A) (htchain₀ : tchain 0 = 𝟙 _)
      (htchain : ∀ n, tchain (n + 1) = tchain n ≫ t n)
      (g₀ : E₀.A ⟶ (E 0).A) (hg₀ : FakeEllipticCurve.IsPullbackVia ι₀ (E 0) E₀ g₀),

      ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (ρ : B →+* ResidueField O) (hρ : Function.Surjective ρ) (hρO : ρ.comp (algebraMap O B) = residue O)
        (E' : FakeEllipticCurve Λ 1 B) (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g'),
        ∀ (n : ℕ), maximalIdeal B ^ (n + 1) = ⊥ →
        ∃ (φ : (R ⧸ maximalIdeal R ^ (n + 1)) →+* B)
          (hφ : ρ.comp φ = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
          (hφO : φ.comp ((Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))).comp (algebraMap O R)) = algebraMap O B)
          (h : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ (E n) E' h ∧ g' ≫ h = g₀ ≫ tchain n ∧

          ∀ (φ' : (R ⧸ maximalIdeal R ^ (n + 1)) →+* B)
            (_ : ρ.comp φ' = ι₀.comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left (0 + 1) n))))
            (_ : φ'.comp ((Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))).comp (algebraMap O R)) = algebraMap O B)
            (h' : E'.A ⟶ (E n).A), FakeEllipticCurve.IsPullbackVia φ' (E n) E' h' → g' ≫ h' = g₀ ≫ tchain n →
            φ' = φ ∧ h' = h := by sorry
