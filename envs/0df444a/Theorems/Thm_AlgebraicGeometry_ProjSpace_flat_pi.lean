-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_pi
-- name    : AlgebraicGeometry.ProjSpace.flat_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/2262ec82-9c57-5f81-9a04-f29d175e570d
-- title:
--   Projective space is flat over its base
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe) and let $n$ be a natural number. Give the polynomial ring $R[x_0,\dots,x_n]$ in $n+1$ variables indexed by `Fin (n + 1)` its standard grading by total degree, whose degree-$d$ piece is the $R$-submodule `MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d` of homogeneous polynomials of degree $d$. The assertion is that the structure morphism $\pi =$ `ProjSpace.π R n` from projective $n$-space $\mathbb{P}^n_R = \operatorname{Proj} R[x_0,\dots,x_n]$ to $\operatorname{Spec} R$ satisfies Mathlib's morphism property `AlgebraicGeometry.Flat`, i.e. it is a flat morphism of schemes: for every point of the source the local ring of the source is a flat module over the local ring of the target, equivalently the property holds affine-locally for the associated ring homomorphisms. There are no further hypotheses: $R$ is an arbitrary commutative ring (no Noetherian, reducedness or nontriviality assumption) and $n$ is arbitrary, including $n = 0$.
--
--   This is the standard flatness of projective space over an arbitrary base, as in EGA II §2.5, and with it the flatness of $\mathbb{P}^n_R \to \operatorname{Spec} R$ available for base-change and descent arguments. It is used in the construction of the ideal cutting out coincidences for framed polarised abelian schemes, in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_flat_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ProjSpace.flat_pi (R : Type u) [CommRing R] (n : ℕ) : Flat (ProjSpace.π R n) := by sorry
