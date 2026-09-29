-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ee2e9383-81b2-5c3a-b919-f32015415699
-- title:
--   Smooth compactly supported convolution over GL₂ of a normed field
-- statement:
--   Let $A$ be a normed field that is also a normed algebra over $\mathbb{R}$, and let $P$ be a real normed space. Equip $\mathrm{GL}_2(A)$ with the Borel $\sigma$-algebra of its topology (this is what `glBorelOf A` unfolds to), and let $\mu_A$ be a measure on $\mathrm{GL}_2(A)$ for that $\sigma$-algebra. Let $\Phi$ be a complex-valued function of a pair of $2\times 2$ arrays of entries over $A$ together with a parameter in $P$, i.e. $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to A) \times (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to A) \times P \to \mathbb{C}$, and assume: $\Phi$ is $C^\infty$ over $\mathbb{R}$, $\Phi$ has compact support, and the topological support of $\Phi$ is contained in the set of triples whose first two arrays have, as matrices, invertible determinant (determinant a unit of $A$). Then, assuming further that $\mu_A$ is finite on compact sets, there exists $F \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to A) \times P \to \mathbb{C}$ which is $C^\infty$ over $\mathbb{R}$, has compact support, has topological support contained in the set of pairs whose array has invertible determinant, and satisfies, for every $g \in \mathrm{GL}_2(A)$ and every $p \in P$, $$F(g, p) = \int_{h} \Phi(h,\ h^{-1}g,\ p)\, d\mu_A(h),$$ where matrices are read as their entry arrays via the identification `Matrix.of` and $h^{-1}g$ is the product in $\mathrm{GL}_2(A)$.
--
--   This is the parametric smoothness statement for a convolution-type fibre integral over $\mathrm{GL}_2(A)$: integrating a smooth compactly supported kernel of two matrix variables along the relation $h \mapsto (h, h^{-1}g)$ produces again a smooth compactly supported function of the remaining matrix variable and of the parameters, still supported away from non-invertible matrices. It is used in the construction of archimedean test factors for twisted orbital integrals, being cited by [`AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe`](thm.html#AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
    (A : Type) [NormedField A] [NormedAlgebra ℝ A]
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    IsFiniteMeasureOnCompacts μA →
    ∃ F : (Fin 2 → Fin 2 → A) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
        ∀ (g : GL (Fin 2) A) (p : P),
          F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) A), p) =
            ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
              Matrix.of.symm ((h⁻¹ * g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A), p) ∂μA := by sorry
