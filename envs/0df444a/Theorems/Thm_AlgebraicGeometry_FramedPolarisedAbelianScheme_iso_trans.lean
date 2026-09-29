-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_trans
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_trans
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/07b58461-48f8-5574-b29b-035e68419bb9
-- title:
--   Transitivity of framed isomorphism of framed polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a commutative ring $S$, and let $X$, $X'$, $X''$ be framed polarised abelian schemes of relative dimension $g$, degree $N+1$ and level $n$ over $S$, i.e. polarised abelian schemes $(A,f\colon A\to\operatorname{Spec} S, L, P, \mathrm{pol},\dots)$ in the sense of `PolarisedAbelianScheme g (N+1) n S` equipped with a projective presentation `frame` of the polarising module `pol` relative to $f$ in $N+1$ homogeneous coordinates whose structure morphism `frame.toProj` is a closed immersion and whose sections form a section basis. The theorem asserts that the relation `FramedPolarisedAbelianScheme.Iso` is transitive: given witnesses of `Iso X X'` and `Iso X' X''`, one obtains a witness of `Iso X X''`. Here `Iso X X'` asserts the existence of an isomorphism of schemes $e\colon X.A \xrightarrow{\ \sim\ } X'.A$ with $X'.f \circ e = X.f$ such that: $X'.\mathtt{frame.toProj} \circ e = X.\mathtt{frame.toProj}$; for every scheme $T$, every $t\colon T\to\operatorname{Spec} S$ and all $T$-points $x,y$ of $X.f$ over $t$, $e \circ (X.L.\mathrm{mul}\ t\ x\ y) = X'.L.\mathrm{mul}\ t\ (e\circ x)\ (e\circ y)$; for each index $i$, $e \circ X.P_i = X'.P_i$; and, locally on the base, the polarising modules agree, in the sense that every point $s \in \operatorname{Spec} S$ has an open neighbourhood $U$ for which the pullback of $X'.\mathrm{pol}$ along $e$ and $X.\mathrm{pol}$ become isomorphic after restriction to $X.f^{-1}(U)$.
--
--   This is the transitivity clause for the framed isomorphism relation on framed polarised abelian schemes, the framed counterpart of the corresponding statement for polarised abelian schemes; together with reflexivity and symmetry it lets the relation be used as an equivalence relation when assembling moduli data. It is used in the construction of reframings over a cover compatible with theta-adapted data ([`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_trans.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_trans
    {g N n : ℕ} {S : Type} [CommRing S] (X X' X'' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') (h' : FramedPolarisedAbelianScheme.Iso X' X'') :
    FramedPolarisedAbelianScheme.Iso X X'' := by sorry
