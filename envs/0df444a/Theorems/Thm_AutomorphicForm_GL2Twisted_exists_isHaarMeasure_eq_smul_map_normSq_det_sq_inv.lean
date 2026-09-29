-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
-- name    : AutomorphicForm.GL2Twisted.exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b89e8684-915a-5b7c-87c7-a3d569de75a7
-- title:
--   Haar measure on GL₂(ℂ⊗_ℝℝ) as |det|⁻⁴ Lebesgue measure
-- statement:
--   Let $\mu$ be a measure on the group $GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ taken with respect to the measurable space `glBorelOf (ℂ ⊗[ℝ] ℝ)`, that is, the Borel $\sigma$-algebra of the topology on $GL_2$ of the topological ring $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}$, and assume $\mu$ is a Haar measure for this measurable space. The assertion is that there exists a constant $c$ in $\mathbb{R}_{\geq 0}$ with $c>0$ such that $\mu$ equals $c$ times the pushforward, along the map described next, of the following measure on the space $\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{C}$ of $2\times 2$ complex entry arrays: Lebesgue measure (on the four complex, hence eight real, coordinates) restricted to the set of arrays $A$ with $\det A\neq 0$, multiplied by the density $A\mapsto \bigl(N(\det A)^2\bigr)^{-1}$, where $N$ is the complex norm form $\mathrm{Complex.normSq}$, so that the density is $|\det A|^{-4}$. The map sends an array $A$ with $\det A\neq 0$ to the invertible matrix it determines, transported entrywise along the inverse of the algebra isomorphism $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$, and sends every array of determinant $0$ to the identity element $1$.
--
--   This is the standard explicit description of Haar measure on $GL_2$ over the completion $\mathbb{C}$ (presented here for $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}$, the shape in which the archimedean factor occurs in the adelic setting): up to a positive scalar it is $|\det g|^{-4}$ times Lebesgue measure in the matrix entries. It is used in the analysis of twisted orbital integrals at an archimedean place, both for the comparison of integrals with integrals over an Iwasawa coordinate chart and for the evaluation of twisted orbital integrals in split and elliptic cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.GL2Twisted.exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    ∃ c : NNReal, 0 < c ∧
      μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)) := by sorry
