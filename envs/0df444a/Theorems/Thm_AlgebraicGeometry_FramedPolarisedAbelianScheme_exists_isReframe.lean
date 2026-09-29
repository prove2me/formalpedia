-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/15dcd932-7e8a-53d5-b00a-bf1bca0a8174
-- title:
--   Reframing a framed polarised abelian scheme by a unit matrix
-- statement:
--   Let $g, N, n$ be natural numbers and $S$ a commutative ring. Let $X$ be a framed polarised abelian scheme of type $(g,N,n)$ over $S$: that is, a polarised abelian scheme with parameters $g$, $N+1$, $n$ over $S$ — an abelian scheme $X.A \to \operatorname{Spec} S$ with commutative relative group law, fibres of dimension $g$, a free basis of $n$-torsion sections indexed by $\mathrm{Fin}(2g)$, and an invertible module `pol` which embeds $X.A$ by its sections and has geometric fibrewise $H^0$ of rank $N+1$ — equipped with a projective presentation `frame` of `pol` over the structure morphism with $N+1$ global sections, whose associated morphism to $\mathbf{P}^N_S = \operatorname{Proj}$ of the graded polynomial ring is a closed immersion, and whose sections satisfy `Scheme.Modules.IsSectionBasis`. Let $U$ be an $(N+1)\times(N+1)$ matrix over $S$ which is a unit in the matrix ring. Then there exists a framed polarised abelian scheme $X'$ of the same type with $X.IsReframe\ U\ X'$: there is a projective presentation $P'$ of `pol`, with $P'.toProj$ a closed immersion and $P'.\sigma$ again a section basis, such that $X'$ is $X$'s underlying polarised abelian scheme framed by $P'$, and $P'.\sigma_i = \sum_j \bar{U}_{ij} \cdot X.frame.\sigma_j$, where $\bar{U}_{ij}$ denotes the image of $U_{ij}$ in $\Gamma(X.A,\top)$ under the structure morphism.
--
--   This is the $GL_{N+1}(S)$-action on theta frames: the projective frame attached to a polarisation may be changed by any invertible matrix of constants, the underlying polarised abelian scheme being unchanged. It underlies the treatment of the theta level structure torsor, and is used in the construction of the finite group action on theta-adapted frames and in the descent arguments that compare reframings on a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe.lean

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    ∃ X' : FramedPolarisedAbelianScheme g N n S, X.IsReframe U X' := by sorry
