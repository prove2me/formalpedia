-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem
-- name    : AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/5829a59f-656c-5cf1-a247-eb7325406e78
-- title:
--   Closed subsets missing the generic point are finite
-- statement:
--   Let $X$ be a scheme (in a fixed universe) which is integral, locally Noetherian and whose underlying topological space is compact, i.e. $X$ is quasi-compact. Assume that for every point $x$ of $X$ the Krull dimension of the local ring $\mathcal{O}_{X,x}$, the stalk of the structure presheaf of $X$ at $x$, satisfies $\dim \mathcal{O}_{X,x} \le 1$ as an element of $\mathbb{N}\cup\{\infty\}$ adjoined a bottom element (so `ringKrullDim` of each stalk is at most $1$). Let $Z$ be a subset of the underlying space of $X$ which is closed and which does not contain the generic point of $X$ (the latter exists because the space of an integral scheme is irreducible and sober). Then $Z$ is a finite set. Note that the hypothesis is on the dimensions of all local rings, not only those at closed points, and that quasi-compactness together with local Noetherianness is what makes the space of $X$ a Noetherian topological space.
--
--   This is the standard fact that a one-dimensional integral Noetherian scheme carries the cofinite topology away from its generic point: every point other than $\eta$ is closed, and closed subsets not containing $\eta$ are finite. It is used in the treatment of the Igusa scheme, where finiteness of the complement of an open subscheme of the generic fibre is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by sorry
