-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl
-- name    : AlgebraicGeometry.Scheme.Hom.finrank_restrict_add_finrank_restrict_of_isCompl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/bbbd10a5-ac9a-5758-a9c9-4ab7faf16e84
-- title:
--   Additivity of finrank over a clopen decomposition of the source
-- statement:
--   Let $Y$ and $S$ be schemes and let $f : Y \to S$ be a morphism which is finite, flat and locally of finite presentation. Let $U$ and $V$ be open subschemes of $Y$ (elements of the frame $Y.Opens$) which are complementary in that lattice: $U \sqcup V = \top$, i.e. $U \cup V = Y$, and $U \sqcap V = \bot$, i.e. $U \cap V = \varnothing$; consequently each of $U$, $V$ is open and closed in $Y$. Let $s$ be a point of $S$. The assertion is the numerical identity
--   $$\operatorname{finrank}_s(\iota_U \text{ followed by } f) + \operatorname{finrank}_s(\iota_V \text{ followed by } f) = \operatorname{finrank}_s(f),$$
--   where $\iota_U : U \to Y$ and $\iota_V : V \to Y$ are the canonical open immersions and $\operatorname{finrank}_s$ denotes Mathlib's `AlgebraicGeometry.Scheme.Hom.finrank`, the rank at the point $s$ of the base of the pushforward of the structure sheaf along the given morphism. Thus the rank function of $f$ at each point of $S$ splits as the sum of the rank functions of the two restricted morphisms $U \to S$ and $V \to S$, which are again finite, flat and locally of finite presentation since $U$ and $V$ are clopen in $Y$.
--
--   This is the additivity of the rank of a finite flat morphism of finite presentation over a decomposition of its source into two disjoint open (hence clopen) pieces; locally over the base it is the statement that a finite flat algebra splits along an idempotent into a product whose ranks add. It is used in the construction of deformation data for good reduction of Jacobians, where it pins down the rank contributions of the individual pieces of a level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.finrank_restrict_add_finrank_restrict_of_isCompl
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (s : S) :
    (U.ι ≫ f).finrank s + (V.ι ≫ f).finrank s = f.finrank s := by sorry
