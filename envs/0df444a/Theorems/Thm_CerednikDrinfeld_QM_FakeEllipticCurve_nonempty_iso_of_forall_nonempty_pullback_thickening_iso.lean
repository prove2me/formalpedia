-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_iso_of_forall_nonempty_pullback_thickening_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_iso_of_forall_nonempty_pullback_thickening_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/176a4ff9-024e-5124-a1b8-b369a1561843
-- title:
--   Invertible modules isomorphic on all thickenings are isomorphic
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, and let $\star:\Lambda\to\Lambda$ satisfy $\mu\,x^{\star}=\bar{x}\,\mu$ for all $x\in\Lambda$. Let $N\in\mathbb{N}$, let $S$ be a commutative ring and $E$ a `FakeEllipticCurve` for $\Lambda$, $N$ over $S$, with structure morphism $E.f$ to $\operatorname{Spec} S$. Let $R$ be a Noetherian local $S$-algebra, complete for the adic topology of its maximal ideal $\mathfrak{m}$, with algebraically closed residue field. For each $k$ let $j_k$ be a morphism from the base change of $E.f$ along $\operatorname{Spec}$ of $S\to R/\mathfrak{m}^{k+1}$ to the base change along $S\to R$, such that $j_k$ followed by the first projection is the first projection, and $j_k$ followed by the second projection is the second projection followed by $\operatorname{Spec}$ of the quotient map $R\to R/\mathfrak{m}^{k+1}$. Finally let $\mathcal{M},\mathcal{M}'$ be modules on the base change of $E.f$ to $R$ which are invertible in the sense that each point has an open neighbourhood $U$ on which the restriction along $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules, and assume that for every $k$ the pullbacks $j_k^{*}\mathcal{M}$ and $j_k^{*}\mathcal{M}'$ are isomorphic, no compatibility between these isomorphisms being required. Then $\mathcal{M}\cong\mathcal{M}'$.
--
--   This is the algebraisation step for invertible modules on the abelian surface attached to a fake elliptic curve over a complete local base: isomorphism on every infinitesimal thickening of the closed fibre forces isomorphism over $R$, in the manner of Grothendieck's existence theorem. It is used in the construction of the canonical polarisation on fake elliptic curves, in particular by the statements establishing that such a polarisation datum is symmetric with trivial kernel and by the corresponding uniqueness result over complete local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_iso_of_forall_nonempty_pullback_thickening_iso.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_iso_of_forall_nonempty_pullback_thickening_iso
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)] [Algebra S R]
    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (𝓜 𝓜' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (hk : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')) :
    Nonempty (𝓜 ≅ 𝓜') := by sorry
