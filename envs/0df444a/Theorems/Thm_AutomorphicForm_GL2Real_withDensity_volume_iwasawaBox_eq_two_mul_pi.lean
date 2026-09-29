-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi
-- name    : AutomorphicForm.GL2Real.withDensity_volume_iwasawaBox_eq_two_mul_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ddd22a6d-5bb4-59ab-8e7d-e040f59e56b9
-- title:
--   Haar mass 2π of the Iwasawa box in GL₂(ℝ)
-- statement:
--   Work on the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of arrays of real entries, equipped with Lebesgue measure `volume` (the product of the four coordinate measures), and form its density transform by the function sending an array $q$ to $(\mathrm{ENNReal.ofReal}(\det(\mathrm{Matrix.of}\,q)^2))^{-1}$, the inverse being taken in $[0,\infty]$, so that the density is $\det(q)^{-2}$ where $q$ is invertible and $+\infty$ where $\det q = 0$. The assertion is that this measure assigns to the set of those $q$ for which there exist $b_1 \in [1,e]$, $b_2 \in [1,e]$, $x \in [0,1]$ and an element $k$ of the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ with
--   $$\mathrm{Matrix.of}\,q = \begin{pmatrix} b_1 & b_1 x \\ 0 & b_2\end{pmatrix} \cdot k$$
--   the value $\mathrm{ENNReal.ofReal}(2\pi)$. Here $[1,e]$ is the closed interval from $1$ to $\mathrm{Real.exp}\,1$, and $k$ is regarded as a matrix through its underlying general linear group element. The same module defines the row-isometry condition on $k \in GL_2(K)$ for a normed field $K$ as $\lVert \det k\rVert = 1$ together with $\lVert x k_{00} + y k_{10}\rVert^2 + \lVert x k_{01} + y k_{11}\rVert^2 = \lVert x\rVert^2 + \lVert y\rVert^2$ for all $x,y$, and the subgroup of $GL_2(K)$ that it cuts out.
--
--   The measure appearing here is, on the invertible matrices, the standard two-sided Haar measure $dY/\det(Y)^2$ of $GL_2(\mathbb{R})$, and the set measured is the Iwasawa box built from the diagonal ranges $[1,e]$, the unipotent range $[0,1]$ and the compact factor; the theorem pins down its Haar mass. It is used in [`AutomorphicForm.map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real`](thm.html#AutomorphicForm.map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real) to fix the normalisation of the archimedean measure on $GL_2(\mathbb{R})$, and thereby the comparison constants in explicit orbital integral formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm

theorem AutomorphicForm.GL2Real.withDensity_volume_iwasawaBox_eq_two_mul_pi :
    ((volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
        fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)
      {q | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
          ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
          Matrix.of q = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      ENNReal.ofReal (2 * Real.pi) := by sorry
