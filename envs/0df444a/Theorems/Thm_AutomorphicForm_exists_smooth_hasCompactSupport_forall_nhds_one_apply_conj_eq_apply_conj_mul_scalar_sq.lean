-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
-- name    : AutomorphicForm.exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/b68047d0-d0a6-509f-ba20-f17d0d0563c3
-- title:
--   Square-root cutoff for conjugation classes on GL₂(ℝ)
-- statement:
--   Let $f : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ be a function which is smooth with compact support in the following sense: there is a function $F$ on the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of $2\times 2$ real matrix entries, infinitely differentiable over $\mathbb{R}$, with $f(g) = F\bigl((g_{ij})_{i,j}\bigr)$ for every $g \in \mathrm{GL}_2(\mathbb{R})$, and $f$ has compact support. Let $d \in \mathbb{R}^\times$. The assertion is that there exists a function $g : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ which is again smooth with compact support in exactly the same sense (it is the restriction to $\mathrm{GL}_2(\mathbb{R})$ of a $C^\infty$ function of the matrix entries, and has compact support), together with a neighbourhood $U$ of the identity $1 \in \mathrm{GL}_2(\mathbb{R})$, such that for every $t \in U$ and every $h \in \mathrm{GL}_2(\mathbb{R})$,
--   $$g(h^{-1} t h) = f\bigl(h^{-1}\,(t\,\delta)(t\,\delta)\,h\bigr),$$
--   where $\delta = \mathrm{Matrix.GeneralLinearGroup.scalar}\,(\mathrm{Fin}\,2)\,d$ is the scalar matrix $d\cdot I_2$ viewed in $\mathrm{GL}_2(\mathbb{R})$. Thus the values of $g$ on conjugates of elements of $U$ are prescribed to be the values of $f$ on the corresponding conjugates of the square of the rescaled element.
--
--   This is the archimedean "square-root cutoff" construction: it converts a test function $f$ on $\mathrm{GL}_2(\mathbb{R})$ into a test function $g$ whose conjugation-invariant data near the identity reproduces that of $f$ at the squared, centrally rescaled argument. It is used in the comparison of twisted orbital integrals with ordinary orbital integrals at the real place, where matching of orbital integrals at $(t\delta)^2$ must be transported to matching at $t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm

theorem AutomorphicForm.exists_smooth_hasCompactSupport_forall_nhds_one_apply_conj_eq_apply_conj_mul_scalar_sq
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (d : ℝˣ) :
    ∃ g : GL (Fin 2) ℝ → ℂ,
      ((∃ G : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
        ∀ s, g s = G (fun i j => (s : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport g) ∧
      ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, ∀ h : GL (Fin 2) ℝ,
        g (h⁻¹ * t * h) =
          f (h⁻¹ * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) * h) := by sorry
