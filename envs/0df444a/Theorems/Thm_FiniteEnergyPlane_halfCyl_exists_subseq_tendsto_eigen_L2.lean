-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_subseq_tendsto_eigen_L2
-- name    : FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen_L2
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T21:24:03.189319+00:00
-- url     : https://prove2.me/theorems/b420eac3-14cd-4bc4-859d-4c490d0f4e17
-- title:
--   Normalized slices of a linear Cauchy–Riemann solution subconverge in $L^2$ to eigenfunctions
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$. Let $S_\infty$ be a $C^\infty$, $1$-periodic loop of symmetric matrices with $S\to S_\infty$ in $C^\infty$. Let $\zeta$ be a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder. Assume $\zeta$ is not identically zero on $(0,\infty)\times\mathbb{R}$ and satisfies $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>0$. Put $F(s)=\int_0^1\|\zeta(s,t)\|^2\,dt$.
--
--   Then there are an eigenvalue $\mu\le\delta_0$ of $-J_0\partial_t-S_\infty$ and an $s_0$ with $F(s)>0$ for all $s\ge s_0$ such that the following holds. For every sequence $s_k\to\infty$ there are a subsequence $s_{k_j}$ and an eigenfunction $e$ of $-J_0\partial_t-S_\infty$ with eigenvalue $\mu$ such that $F(s_{k_j})^{-1/2}\,\zeta(s_{k_j},\cdot)\to e$ in $L^2(0,1)$.
--
--   This is the $L^2$ form of the qualitative asymptotic description of such solutions (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Theorem 4.8.2 and Lemma 4.8.11). It is used for the uniform version `FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen`.
--
--   **Formalization Note** No rate of convergence of $S$ and no nondegeneracy of $S_\infty$ is assumed. The eigenfunction is `IsLoopEigen Sinf μ e`. The subsequence is `σ ∘ φ` with `φ` strictly monotone, and the convergence is `∫₀¹ ‖(Real.sqrt F)⁻¹ • ζ (σ (φ k), t) - e t‖² → 0`, with $F$ the interval integral over $[0,1]$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 4.8.2 and Lemmas 4.8.8, 4.8.11

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder, with `S(s, t) → S∞(t)` in `C^∞`,
not identically zero and with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`: there is an eigenvalue `μ ≤ δ₀` of
`-J₀ ∂ₜ - S∞` such that the slices `ζ(s, ·)` are eventually nonzero in `L²` and, along every
sequence `sₖ → ∞`, a subsequence of the `L²`-normalized slices converges in `L²(0, 1)` to an
eigenfunction with eigenvalue `μ`. -/
theorem halfCyl_exists_subseq_tendsto_eigen_L2 {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ : ℝ, (∀ s ≥ s₀, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) ∧
      ∀ σ : ℕ → ℝ, Tendsto σ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
          Tendsto (fun k : ℕ => ∫ t in (0:ℝ)..1,
            ‖(Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t) - e t‖ ^ 2)
            atTop (𝓝 0) := by
  sorry

end FiniteEnergyPlane
