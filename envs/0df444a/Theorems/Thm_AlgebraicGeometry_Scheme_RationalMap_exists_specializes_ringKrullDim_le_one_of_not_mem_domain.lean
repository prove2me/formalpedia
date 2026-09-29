-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain
-- name    : AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b860b9a4-7bba-5949-8ed1-6f32905efee7
-- title:
--   Indeterminacy of a rational map to an affine target occurs in codimension one
-- statement:
--   Let $X$ and $Y$ be schemes. Assume $X$ is integral and locally Noetherian, and that for every point $x$ of $X$ the local ring $\mathcal{O}_{X,x}$ (the stalk of the structure sheaf) is integrally closed in its field of fractions; assume $Y$ is affine. Let $u \colon X \dashrightarrow Y$ be a rational map, with `u.domain` its domain of definition, the open subset of $X$ on which $u$ is represented by a morphism of schemes. Let $x$ be a point of $X$ lying outside `u.domain`. Then there is a point $z$ of $X$ which also lies outside `u.domain`, which specialises to $x$ (that is, $\mathcal{N}_z \le \mathcal{N}_x$ as filters, so that $x$ lies in the closure of $\{z\}$), and whose local ring satisfies $\operatorname{ringKrullDim} \mathcal{O}_{X,z} \le 1$ in $\mathbb{N}_\infty$ extended by a bottom element. No bound on the dimension of $X$ is assumed, and the conclusion asserts existence of one such $z$ rather than a description of all components of the indeterminacy locus.
--
--   This is the purity statement for the indeterminacy locus of a rational map from a normal integral scheme into an affine scheme (Bosch–Lütkebohmert–Raynaud, Lemma 4.4/2; EGA IV 20.4.12): the complement of the domain of definition can only be approached from points of codimension at most one, so such a rational map has no indeterminacy in codimension $\ge 2$. It is used, together with the unique-extension result [`AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk`](thm.html#AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk), in the construction of the group law on a Jacobian with good reduction and in the study of invertibility of pullback sections over affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain.lean

import Mathlib
import Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) [IsAffine Y]
    (u : X ⤏ Y) (x : X) (hx : x ∉ u.domain) :
    ∃ z : X, z ∉ u.domain ∧ z ⤳ x ∧ ringKrullDim (X.presheaf.stalk z) ≤ 1 := by sorry
