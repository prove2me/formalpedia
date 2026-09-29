-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/4277bd40-ccdf-5041-8436-6595cf147df1
-- title:
--   Canonical polarisation data agreeing on the closed fibre, 2 invertible
-- statement:
--   Fix primes $q \neq q'$ and rationals $a, b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a > 0$ or $b > 0$, and a finite place $v$ of $\mathbb{Q}$ splits no nonzero element (all nonzero elements of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ being units) exactly when $v$ lies above $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$ and finitely generated, maximal among such), let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\star : \Lambda \to \Lambda$ satisfy $\mu \cdot \star(x) = \bar{x} \cdot \mu$ for all $x \in \Lambda$, where $\bar{\ }$ is quaternionic conjugation. Let $N$ be a natural number and $S$ a local Artinian commutative ring in which $2$ is a unit, and let $E$ be a fake elliptic curve over $S$ of level $N$ for $\Lambda$: an abelian scheme $f : A \to \operatorname{Spec} S$ with commutative relative group law, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base compatible with the group law and satisfying the trace condition, together with the remaining level and curve data of the structure. Let $\mathcal{L}, \mathcal{L}'$ be modules on $E.A$, each a canonical polarisation datum for $\star$, that is: invertible, satisfying `IsSymmetric` and `KernelIsTwoTorsion` for $E.L$, admitting after some faithfully flat base change $S \to S'$ a square root up to `LocIsoOnBase` in the sense of `IsCanonicalPolData`, having strictly positive $H^0$-rank on every geometric fibre, and `RosatiCompatible` with the $\Lambda$-action and $\star$. Assume that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ along the first projection of $A \times_{\operatorname{Spec} S} \operatorname{Spec}(S/\mathfrak{m})$ are isomorphic locally on the base $\operatorname{Spec}(S/\mathfrak{m})$. Then $\mathcal{L}$ and $\mathcal{L}'$ are isomorphic locally on $\operatorname{Spec} S$: every point of $\operatorname{Spec} S$ has an open neighbourhood $U$ with the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $f^{-1}(U)$ isomorphic.
--
--   This is the rigidity step for canonical polarisations on fake elliptic curves over an Artinian local base: a canonical polarisation datum is determined, locally on the base, by its restriction to the closed fibre when $2$ is invertible. It feeds the comparison of canonical polarisations over complete local bases with algebraically closed residue field used in the Čerednik–Drinfeld description of the Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_residue_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) [IsLocalRing S] [IsArtinianRing S] (E : FakeEllipticCurve Λ N S)
    (𝓛 𝓛' : E.A.Modules) (h : E.IsCanonicalPol star 𝓛) (h' : E.IsCanonicalPol star 𝓛')
    (hres : LocIsoOnBase (pullback.snd E.f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))
      ((Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))).obj 𝓛)
      ((Scheme.Modules.pullback (pullback.fst E.f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))))).obj 𝓛')) :
    LocIsoOnBase E.f 𝓛 𝓛' := by sorry
