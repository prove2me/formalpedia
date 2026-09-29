-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
-- name    : AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/2fc8c93a-e519-5a88-abd6-e95185fde30d
-- title:
--   Bijectivity of restriction Γ(V)→Γ(V∩ U) (algebraic Hartogs)
-- statement:
--   Let $X$ be a scheme (in a fixed universe) that is locally Noetherian, and let $V,U$ be open subsets of $X$. Assume that $X$ is normal along $V$, in the sense that for every point $x$ of $X$ lying in $V$ the local ring $\mathcal{O}_{X,x}$, taken as the stalk of the structure presheaf at $x$, is an integral domain and is integrally closed in its fraction field; assume further that $U$ contains every point $x$ of $V$ whose local ring has Krull dimension at most $1$, the dimension being measured by `ringKrullDim` with values in the extended naturals, so that the closed subset $V\setminus U$ of $V$ has codimension at least $2$ at each of its points. The conclusion is that the restriction map $\Gamma(X,V)\to\Gamma(X,V\cap U)$ obtained by applying the structure presheaf to the inclusion $V\cap U\le V$ (via `inf_le_left`) is bijective as a map of underlying sets: every section over $V\cap U$ extends to $V$, and the extension is unique.
--
--   This is the sections form of the algebraic Hartogs extension lemma: on a normal locally Noetherian scheme, regular functions extend uniquely across closed subsets of codimension at least two, the hypotheses being imposed only at points of $V$. It is used in the construction of Deligne–Rapoport resolved models of modular curves, where invertibility of sheaves and isomorphisms of open pullbacks are checked after removing loci of codimension at least two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V U : X.Opens)
    (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by sorry
