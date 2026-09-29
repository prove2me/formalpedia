-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_isSymmetric_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.isSymmetric_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/890d1d35-e0fe-528a-9a2f-a4202d78d631
-- title:
--   Symmetry of the polarisation is stable under base change
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and commutative rings $S$, $S'$, and let $\varphi : S \to S'$ be a ring homomorphism. Let $u$ be a polarised abelian scheme of invariants $(g,d,n)$ over $S$ and $u'$ one over $S'$; each consists of a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ (multiplication, unit and inverse on $T$-points over the base, natural in $T$) that is commutative, the property bundle `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections of $f$ that are $n$-torsion, independent and spanning the $n$-torsion on geometric fibres, and an invertible module `pol` admitting a closed immersion by sections over the base whose geometric fibre $H^0$ has rank $d$ at every algebraically closed point. Assume $u'$ is obtained from $u$ by base change along $\varphi$, i.e. there is a morphism $g_A : u'.A \to u.A$ making the square with $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ cartesian, compatible with the group laws on $T$-points, carrying each $P'_i$ to $P_i$ composed with $\operatorname{Spec}\varphi$, and with $g_A^{*}(u.\mathrm{pol}) \cong u'.\mathrm{pol}$. Assume further that $u.\mathrm{pol}$ is symmetric in the sense that for every point $s$ of $\operatorname{Spec} S$ there is an open $U \ni s$ over which the restrictions of $[-1]^{*}(u.\mathrm{pol})$ and $u.\mathrm{pol}$ to $u.f^{-1}U$ are isomorphic, $[-1]$ being the inversion morphism of $u.L$. The conclusion is that $u'.\mathrm{pol}$ is symmetric in the same sense over $\operatorname{Spec} S'$.
--
--   This is the base-change stability of symmetry of a polarising line bundle on an abelian scheme, symmetry being formulated as a Zariski-local isomorphism $[-1]^{*}\mathcal L \cong \mathcal L$ over the base. It feeds the corresponding base-change statement for polarised abelian schemes carrying the symmetry and rootedness conditions, [`AlgebraicGeometry.PolarisedAbelianScheme.rootedSymmetricOfType_of_isPullback`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.rootedSymmetricOfType_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_isSymmetric_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.isSymmetric_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : Polarisation.IsSymmetric u.f u.L u.pol) :
    Polarisation.IsSymmetric u'.f u'.L u'.pol := by sorry
