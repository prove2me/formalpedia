-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
-- name    : AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a0585998-e021-5647-a132-621a84c0055e
-- title:
--   Proper closed subsets of a Noetherian integral curve are finite
-- statement:
--   Let $X$ be a scheme which is integral (irreducible with reduced structure, so that its underlying space has a generic point `genericPoint X`) and whose underlying topological space is Noetherian, i.e. satisfies the ascending chain condition on open sets. Assume the one-dimensionality hypothesis that every point $x$ of $X$ other than the generic point has closed singleton $\{x\}$. The conclusion is that for every subset $Z$ of the underlying space of $X$ which is closed and is not all of $X$, the set $Z$ is finite. Thus all proper closed subsets of such an $X$ are finite sets, necessarily consisting of closed points; the statement is about the underlying topological space only, the scheme structure entering through integrality (irreducibility, giving the generic point) and sobriety of schemes.
--
--   This is the standard topological form of the statement that a Noetherian integral scheme of dimension at most one has only finite proper closed subsets, the "curve hypothesis" in the form used for models of modular curves. It is invoked in the construction of lifts along degeneracy maps for rational curve models and in the proof that certain sets of closed points of such a model are infinite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (hdim : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X)) :
    ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite := by sorry
