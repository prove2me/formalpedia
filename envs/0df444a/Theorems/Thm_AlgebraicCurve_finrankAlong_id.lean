-- Prove2me | Theorems.Thm_AlgebraicCurve_finrankAlong_id
-- name    : AlgebraicCurve.finrankAlong_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ff8c39ca-cd7f-596b-a3e2-167bc38c196c
-- title:
--   Degree along the identity is 1
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. For a $K$-algebra homomorphism $\varphi : F \to F'$ of fields over $K$, the quantity [`AlgebraicCurve.finrankAlong`](def/AlgebraicCurve_Correspondence.html#L51) $K\,\varphi$ is defined to be the $F$-module rank $\mathrm{finrank}_F F'$ of the target, where $F'$ is regarded as an $F$-algebra via the ring homomorphism underlying $\varphi$ (the instance [`AlgebraicCurve.algebraAlong`](def/AlgebraicCurve_Correspondence.html#L14)); in the language of curves given by their function fields this is the degree of the corresponding morphism. The assertion is that for the identity $K$-algebra homomorphism `AlgHom.id K F` of $F$ this number equals $1$: the $F$-module structure on $F$ transported along the identity is the standard one, and $\mathrm{finrank}_F F = 1$. No hypotheses beyond the field and $K$-algebra structures are imposed; in particular nothing is assumed about transcendence degree, so the statement is purely about ranks of one-dimensional modules and not about curves as such.
--
--   This records the normalisation that the identity morphism of a curve has degree $1$ in the `finrankAlong` bookkeeping used throughout the treatment of correspondences between modular function fields. It is invoked wherever a composite of morphisms degenerates to the identity, for instance in the divisor identities relating pullback and pushforward along the maps used to define Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrankAlong_id.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.finrankAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] : AlgebraicCurve.finrankAlong K (AlgHom.id K F) = 1 := by sorry
