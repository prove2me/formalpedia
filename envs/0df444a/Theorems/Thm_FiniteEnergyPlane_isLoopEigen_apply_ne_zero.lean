-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
-- name    : FiniteEnergyPlane.isLoopEigen_apply_ne_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T22:24:04.042927+00:00
-- url     : https://prove2.me/theorems/94203606-187a-4132-a9f6-8a0bc7216aac
-- title:
--   Eigenfunctions of the loop operator $-J_0\partial_t-S_\infty$ vanish nowhere
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be continuous and $\mu\in\mathbb{R}$. Let $e:\mathbb{R}\to\mathbb{R}^{2n}$ be a $C^\infty$, $1$-periodic map, not identically zero, with $-J_0\,e'(t)-S_\infty(t)\,e(t)=\mu\,e(t)$ for all $t$, where $J_0=\begin{pmatrix}0&-I\\ I&0\end{pmatrix}$. Then $e(t)\neq0$ for every $t\in\mathbb{R}$.
--
--   So an eigenfunction of the operator $-J_0\frac{d}{dt}-S_\infty$ on loops vanishes nowhere. It is used for Wendl's Corollary 4.8.3, which says that solutions of linear Cauchy–Riemann equations have no zeros near infinity.
--
--   **Formalization Note** The eigenfunction hypothesis is `IsLoopEigen Sinf μ e`. Only continuity of $S_\infty$ is assumed: neither symmetry nor periodicity of $S_\infty$ is required.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, proof of Corollary 4.8.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

/-- An eigenfunction of `-J₀ ∂ₜ - S∞` (for a continuous loop `S∞`) vanishes nowhere. -/
theorem isLoopEigen_apply_ne_zero {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : Continuous Sinf) (μ : ℝ) (e : ℝ → CauchyRiemannIndex.Vec n)
    (he : IsLoopEigen Sinf μ e) (t : ℝ) : e t ≠ 0 := by
  sorry

end FiniteEnergyPlane
