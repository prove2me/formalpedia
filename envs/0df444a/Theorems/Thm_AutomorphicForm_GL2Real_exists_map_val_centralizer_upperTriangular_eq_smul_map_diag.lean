-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
-- name    : AutomorphicForm.GL2Real.exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/48c43146-02cf-5688-bf3f-efebf7713af9
-- title:
--   Haar measure on a split maximal torus of GL₂(ℝ)
-- statement:
--   Let $a_1,a_2$ be real numbers with $a_1a_2\neq 0$ and $a_1\neq a_2$, and write $\gamma = \mathrm{upperTriangular}\,a_1\,a_2\,0$ for the element of $GL_2(\mathbb{R})$ given by the matrix $!![a_1,0;0,a_2]$, invertible because its determinant $a_1a_2$ is nonzero. Let $T =$ `Subgroup.centralizer {γ}` be the centraliser of $\gamma$ in $GL_2(\mathbb{R})$, equipped with the Borel $\sigma$-algebra `centralizerBorel ℝ γ` of its subspace topology, and let $\tau$ be a measure on $T$ which is a Haar measure for this measurable structure. The assertion is that there exists $c \in \mathbb{R}_{\geq 0}$ with $c>0$ such that the pushforward of $\tau$ along the inclusion `Subtype.val : T → GL (Fin 2) ℝ`, the target carrying the Borel $\sigma$-algebra `glBorelOf ℝ`, is equal to $c$ times the pushforward, along the map $\alpha = (\alpha_1,\alpha_2) \mapsto \mathrm{upperTriangular}\,\alpha_1\,\alpha_2\,0$ where $\alpha_1\alpha_2 \neq 0$ and $\mapsto 1$ otherwise, of the measure on $\mathbb{R}\times\mathbb{R}$ obtained from Lebesgue measure restricted to $\{\alpha : \alpha_1\alpha_2 \neq 0\}$ by taking the density $|\alpha_1\alpha_2|^{-1}$.
--
--   This identifies, up to a positive scalar, any Haar measure on the split maximal torus centralising a regular split semisimple element of $GL_2(\mathbb{R})$ with the explicit model $d\alpha_1\,d\alpha_2/|\alpha_1\alpha_2|$ in diagonal coordinates, pushed forward to $GL_2(\mathbb{R})$. It is used to evaluate orbital integrals at split elements in explicit coordinates, both in the real and in the twisted setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory
open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem
    AutomorphicForm.GL2Real.exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (hne : a₁ ≠ a₂)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) (glBorelOf ℝ) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by sorry
