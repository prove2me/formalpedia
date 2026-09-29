-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_locIsoOnBase_of_isCanonicalPolData_of_isCanonicalPolData_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.locIsoOnBase_of_isCanonicalPolData_of_isCanonicalPolData_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/817e35a3-c9c3-565d-b0f4-399c14e4037d
-- title:
--   Local uniqueness of canonical polarisation data for QM surfaces
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and a finite place $v$ of $\mathbb{Q}$ has the property that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ lies above $q$ or above $q'$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order not properly contained in any order), let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, let $\star\colon\Lambda\to\Lambda$ satisfy $\mu\,\star(x)=\bar{x}\,\mu$ for all $x\in\Lambda$, and let $\beta\colon\mathrm{Fin}(2\cdot 2)\to\Lambda$. Let $d,m\in\mathbb{N}$, let $S$ be a commutative ring in which $2$ is a unit, let $X$ be a polarised abelian scheme over $S$ with fibres of dimension $2$, polarisation degree $d$ and full level $m$, and let $t$ be a `QMStructure` for $(\Lambda,\star,\beta)$ on $X$, so in particular $t$ provides a $\Lambda$-action `t.act` on $X.A$ over $S$. Let $\mathcal{L},\mathcal{L}'$ be module objects on $X.A$ each satisfying `IsCanonicalPolData X.f X.L t.act t.act_over star`, that is: each is invertible; each is symmetric in the sense that its pullback along the inversion morphism is isomorphic to it locally on the base; for each, the slice of the Mumford bundle at a point over any affine base change is trivial locally on the base precisely for the $2$-torsion points; each becomes, after a faithfully flat base extension $S\to S'$ and for every relative group law on the base change compatible with the given multiplication, locally isomorphic to $\mathcal{L}_0\otimes[-1]^*\mathcal{L}_0$ for some invertible $\mathcal{L}_0$ with trivial kernel; each has strictly positive $H^0$ rank on every geometric fibre; and each is Rosati-compatible with the $\Lambda$-action and $\star$. The conclusion is `LocIsoOnBase X.f` $\mathcal{L}\,\mathcal{L}'$: every point $s\in\operatorname{Spec}S$ has an open neighbourhood $U$ such that the pullbacks of $\mathcal{L}$ and $\mathcal{L}'$ to $X.f^{-1}(U)$ are isomorphic.
--
--   This is the uniqueness, locally on the base, of the canonical polarisation datum attached to a quaternionic multiplication structure on an abelian surface, transferred from the fake-elliptic-curve formulation to the polarised-abelian-scheme formulation used in the Čerednik–Drinfeld uniformisation of Shimura curves. It is used in the construction of the pullback diagrams comparing QM structures over $S$ with those over localisations, under the standing hypothesis that $2$ is invertible on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_locIsoOnBase_of_isCanonicalPolData_of_isCanonicalPolData_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.locIsoOnBase_of_isCanonicalPolData_of_isCanonicalPolData_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) {d m : ℕ} {S : Type} [CommRing S] (h2 : IsUnit (2 : S))
    (X : PolarisedAbelianScheme 2 d m S) (t : QMStructure Λ star β X)
    (𝓛 𝓛' : X.A.Modules)
    (h : CerednikDrinfeld.QM.IsCanonicalPolData X.f X.L t.act t.act_over star 𝓛)
    (h' : CerednikDrinfeld.QM.IsCanonicalPolData X.f X.L t.act t.act_over star 𝓛') :
    LocIsoOnBase X.f 𝓛 𝓛' := by sorry
