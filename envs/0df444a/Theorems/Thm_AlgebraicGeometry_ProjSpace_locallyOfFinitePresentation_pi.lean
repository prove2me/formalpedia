-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi
-- name    : AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/cca628bd-396f-5d97-9cf0-e27ead5bcd41
-- title:
--   Projective space is locally of finite presentation
-- statement:
--   For every commutative ring $R$ (in a fixed universe) and every natural number $n$, the structure morphism $\pi : \mathbb{P}^n_R \to \operatorname{Spec} R$ of projective $n$-space over $R$, i.e. `ProjSpace.π R n`, where $\mathbb{P}^n_R$ is the $\operatorname{Proj}$ of the polynomial ring $R[x_0,\dots,x_n]$ with its standard grading by total degree (the graded algebra structure coming from `MvPolynomial.homogeneousSubmodule (Fin (n+1)) R`), satisfies Mathlib's predicate `LocallyOfFinitePresentation`: it is locally of finite presentation as a morphism of schemes. There are no further hypotheses: $R$ is an arbitrary commutative ring, not assumed Noetherian, so the assertion is finite presentation rather than merely finite type, and the statement is the absolute one over the base $\operatorname{Spec} R$ rather than a relative statement about a morphism over $\mathbb{P}^n_R$.
--
--   This is the standard fact that projective space over any base ring is locally of finite presentation (EGA IV, Stacks 01TW), here in the affine-base form. It serves as an input to the study of framed polarised abelian schemes, being used in the construction of a finitely generated ideal cutting out a locus where translates satisfy a pullback condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_pi (R : Type u) [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (ProjSpace.π R n) := by sorry
