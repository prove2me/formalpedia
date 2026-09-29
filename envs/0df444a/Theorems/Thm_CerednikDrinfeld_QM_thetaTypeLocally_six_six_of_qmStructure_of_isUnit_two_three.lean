-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_thetaTypeLocally_six_six_of_qmStructure_of_isUnit_two_three
-- name    : CerednikDrinfeld.QM.thetaTypeLocally_six_six_of_qmStructure_of_isUnit_two_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/cc37133e-460b-5ea5-b0e2-cbf08db5491f
-- title:
--   QM structures force local theta type (6,6)
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $star:\Lambda\to\Lambda$ and a family $\beta:\mathrm{Fin}(2\cdot 2)\to\Lambda$; let $m\ge 3$ be a natural number, let $\mathcal{O}$ be a commutative ring in which $m$, $2$ and $3$ are units, let $S$ be a commutative ring equipped with a morphism $s:\operatorname{Spec} S\to\operatorname{Spec}\mathcal{O}$, and assume the entries of $![6,6]$ are nonzero. Let $X$ be a polarised abelian scheme of type $(2,36,m)$ over $S$: a scheme $A$ with a structure morphism to $\operatorname{Spec} S$, a commutative relative group law, the property bundle of an abelian scheme, all fibres of Krull dimension $2$, four sections $P_i$ that are $m$-torsion and freely generate the geometric $m$-torsion, and an invertible module $pol$ which is very ample in the sense of defining a closed immersion by its sections and has geometric fibre $H^0$-rank $36$. Let $\sigma$ be a $\mathrm{QMStructure}$ for $(\Lambda,star,\beta)$ on $X$: an action of $\Lambda$ by endomorphisms of $A$ over $S$ which are group-law homomorphisms, send $1$ to the identity, satisfy $act(xy)=act(x)\circ act(y)$ and additivity in $x$, have tangential trace $n$ whenever $x+x^{*}=n$, together with a section $P$ with $act(\beta_j)(P)=P_j$ and a canonical polarisation datum $polE$ relative to $star$ with $pol$ locally isomorphic on the base to $polE\otimes polE\otimes polE$. Then $X$ satisfies $\mathrm{ThetaTypeLocally}$ for $\delta=![6,6]$ with $N=35$: for every commutative $S$-algebra $R$ and every $\zeta\in R$ with $\zeta^{36}=1$ and $1-\zeta^{j}$ a unit for $0<j<36$, there is a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme $X'$ of type $(2,35,m)$ over $R'$ and a bijection $\mathrm{Fin}\,36\simeq \mathbb{Z}/6\times\mathbb{Z}/6$ such that $X$ pulls back to $X'$ along $S\to R\to R'$ and $X'$ satisfies `IsThetaAdapted` for $\delta$ and that bijection.
--
--   This is the passage from quaternionic multiplication to theta structures of type $(6,6)$ on a polarised abelian surface of degree $36$ with full level-$m$ structure: after an étale faithfully flat base change the surface acquires a theta-adapted frame. It supplies the hypothesis on the moduli property $Q=\mathrm{ThetaTypeLocally}\,![6,6]$ used in the fine moduli statement for quaternionic surfaces in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_thetaTypeLocally_six_six_of_qmStructure_of_isUnit_two_three.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem CerednikDrinfeld.QM.thetaTypeLocally_six_six_of_qmStructure_of_isUnit_two_three
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {m : ℕ} (hm : 3 ≤ m) (𝒪 : Type) [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪)) (h2 : IsUnit (2 : 𝒪)) (h3 : IsUnit (3 : 𝒪))
    {S : Type} [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    [h66 : ∀ i : Fin 2, NeZero ((![6, 6] : Fin 2 → ℕ) i)]
    (X : PolarisedAbelianScheme 2 36 m S) (σ : QMStructure Λ star β X) :
    PolarisedAbelianScheme.ThetaTypeLocally (N := 35) ![6, 6] S X := by sorry
