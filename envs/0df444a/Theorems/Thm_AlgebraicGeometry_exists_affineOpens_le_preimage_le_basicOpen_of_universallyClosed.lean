-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed
-- name    : AlgebraicGeometry.exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/7d9ef85b-0377-5893-bf67-cb5196b3de29
-- title:
--   Affine neighbourhood on which a section is invertible along fibres
-- statement:
--   Let $X$ and $Y$ be schemes and let $p : X \to Y$ be a morphism which is universally closed. Let $U$ be an open subset of $Y$, let $y$ be a point of $Y$ lying in $U$, and let $s$ be a section of the structure sheaf of $X$ over the open preimage $p^{-1}U$. Assume that every point $x$ of $X$ whose image $p(x)$ equals $y$ lies in the basic open subset $X_s = \{x \in p^{-1}U : s(x) \neq 0 \text{ in the residue field}\}$, i.e. $s$ vanishes nowhere on the fibre over $y$. The conclusion asserts the existence of an affine open subset $V$ of $Y$ (an element of the subtype of affine opens of $Y$) such that $y \in V$, $V \subseteq U$, and the preimage $p^{-1}V$ is contained in the basic open $X_s$. Thus $s$ vanishes at no point of $X$ lying over $V$; the statement records the containment of opens and not, in addition, the resulting invertibility of the restriction of $s$ to $p^{-1}V$.
--
--   This is the standard local-on-the-base manoeuvre accompanying universally closed (for instance finite) morphisms: nonvanishing of a section along one fibre spreads out to an affine neighbourhood of the base point. It is used in the construction of eigen-subdata for abelian schemes, where it supplies an affine open over which a chosen section becomes a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed
    {X Y : Scheme.{u}} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
    (s : Γ(X, p ⁻¹ᵁ U)) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ p ⁻¹ᵁ V.1 ≤ X.basicOpen s := by sorry
