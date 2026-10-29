-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoUniformly_isLoopEigen
-- name    : FiniteEnergyPlane.exists_subseq_tendstoUniformly_isLoopEigen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:00:19.084964+00:00
-- url     : https://prove2.me/theorems/cc686244-bdf4-4d79-87d5-e2bb532b3897
-- title:
--   Normalized approximate eigenfunctions of the asymptotic loop operator subconverge uniformly to an eigenfunction
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be a $C^\infty$, $1$-periodic loop of symmetric matrices and let $\mu\in\mathbb{R}$. Let $f_k:\mathbb{R}\to\mathbb{R}^{2n}$ be $C^1$ and $1$-periodic, with
--   $$\int_0^1\|f_k(t)\|^2\,dt=1\quad\text{for all }k,\qquad \int_0^1\big\|-J_0f_k'(t)-S_\infty(t)f_k(t)-\mu f_k(t)\big\|^2\,dt\longrightarrow0 .$$
--
--   Then a subsequence of $(f_k)$ converges uniformly on $\mathbb{R}$ to an eigenfunction $e$ of the asymptotic operator $-J_0\partial_t-S_\infty$ with eigenvalue $\mu$: $e$ is $C^\infty$, $1$-periodic, not identically zero, and $-J_0e'-S_\infty e=\mu e$.
--
--   This is the compactness property of approximate eigenfunctions of the asymptotic operator (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Section 3.5). It is stated for loops in $\mathbb{R}^{2n}$ with the $L^2$ norm on one period and is meant for reuse wherever normalized loops with vanishing residual must produce an eigenfunction.
--
--   **Formalization Note** The derivative of $f_k$ is supplied as a continuous function `f' k` with `HasDerivAt (f k) (f' k t) t` for all `t`. The eigenfunction is `IsLoopEigen Sinf μ e`, and the subsequence is `f ∘ φ` with `φ` strictly monotone, converging by `TendstoUniformly` on `ℝ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Section 3.5

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `S∞` be a smooth loop of symmetric matrices and `μ ∈ ℝ`. A sequence of `C¹`, `1`-periodic
loops `fₖ` with `∫₀¹ ‖fₖ‖² = 1` and `∫₀¹ ‖-J₀ fₖ' - S∞ fₖ - μ fₖ‖² → 0` has a subsequence
converging uniformly on `ℝ` to an eigenfunction of `-J₀ ∂ₜ - S∞` with eigenvalue `μ`. -/
theorem exists_subseq_tendstoUniformly_isLoopEigen {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) (f f' : ℕ → ℝ → CauchyRiemannIndex.Vec n)
    (hf : ∀ k t, HasDerivAt (f k) (f' k t) t) (hf' : ∀ k, Continuous (f' k))
    (hper : ∀ k, Function.Periodic (f k) 1)
    (hnorm : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 = 1)
    (hres : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoUniformly (fun k => f (φ k)) e atTop := by
  sorry

end FiniteEnergyPlane
