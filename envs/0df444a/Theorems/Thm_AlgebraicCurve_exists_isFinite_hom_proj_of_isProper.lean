-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper
-- name    : AlgebraicCurve.exists_isFinite_hom_proj_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/5df55d68-9a19-5e30-8507-e0a6aeb9030f
-- title:
--   A proper smooth curve admits a finite map to P¹_K
-- statement:
--   Let $K$ be a field and let $C$ be a scheme, equipped with a morphism $c : C \to \operatorname{Spec} K$, such that $C$ is integral, $c$ is proper, and $c$ is smooth of relative dimension $1$. Then, with $K[X_0,X_1] = \mathrm{MvPolynomial}\ (\mathrm{Fin}\ 2)\ K$ carried by its standard grading by total degree (the homogeneous submodules `MvPolynomial.homogeneousSubmodule (Fin 2) K`), there exists a morphism of schemes $\varphi : C \to \operatorname{Proj} K[X_0,X_1] = \mathbb{P}^1_K$ which is a finite morphism. No hypothesis is imposed on $K$: it need not be algebraically closed, perfect, or of any particular characteristic, and no geometric irreducibility or connectedness assumption beyond integrality of $C$ is made. The assertion is existence only; the morphism $\varphi$ is not claimed to be compatible with the structure morphisms to $\operatorname{Spec} K$, nor is its degree controlled.
--
--   This is the classical fact that a proper smooth integral curve over a field admits a finite morphism to the projective line, obtained from a non-constant rational function whose associated rational map extends by the valuative criterion and is finite because it is proper with finite fibres. Within this development it feeds [`AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field`](thm.html#AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field), the statement that any finite set of points of such a curve lies in a common affine open, via pullback of a suitable affine open of $\mathbb{P}^1_K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.exists_isFinite_hom_proj_of_isProper
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := K)
    ∃ φ : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K), IsFinite φ := by sorry
