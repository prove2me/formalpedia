-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
-- name    : AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f1c43bd0-400d-54f1-bd1b-5c3851267e5b
-- title:
--   Krull dimension of stalks is an open-immersion invariant
-- statement:
--   Let $U$ and $X$ be schemes in a fixed universe, let $i \colon U \to X$ be a morphism of schemes which is an open immersion, and let $u$ be a point of (the underlying topological space of) $U$. The assertion is an equality in the extended natural numbers $\mathbb{N} \cup \{\pm\infty\}$ used by `ringKrullDim`: the Krull dimension of the stalk of the structure sheaf of $U$ at $u$ equals the Krull dimension of the stalk of the structure sheaf of $X$ at the image point $i(u)$ under the continuous map underlying $i$. Both sides are the Krull dimensions of the local rings $\mathcal{O}_{U,u}$ and $\mathcal{O}_{X,i(u)}$, taken as commutative rings; no finiteness, noetherianness or further hypothesis on $U$, $X$ or $i$ is imposed.
--
--   This is the standard fact that an open immersion induces isomorphisms on stalks, hence preserves the dimension of local rings, so that the local dimension of a scheme may be computed on any open chart containing the point. It is used in the project to bound the Krull dimensions of stalks of schemes built by gluing charts, in particular in the verification that regular models of modular curves over a discrete valuation ring have stalks of dimension at most two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (X.presheaf.stalk (i.base u)) := by sorry
