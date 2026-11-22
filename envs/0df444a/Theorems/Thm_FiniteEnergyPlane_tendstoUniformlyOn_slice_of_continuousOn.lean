-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoUniformlyOn_slice_of_continuousOn
-- name    : FiniteEnergyPlane.tendstoUniformlyOn_slice_of_continuousOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:44:37.778803+00:00
-- url     : https://prove2.me/theorems/03ba24e4-a2f4-4a32-a7b2-ab18e047b54b
-- title:
--   Uniform convergence of slices of a continuous map on closed discs
-- statement:
--   Let $F$ be a real normed space, $I\subseteq\mathbb{R}$ open, $G:\mathbb{R}\times\mathbb{C}\to F$ continuous on $I\times\mathbb{C}$, $t_0\in I$, $R\in\mathbb{R}$ and $\tau_k\to t_0$. Then $G(\tau_k,\cdot)\to G(t_0,\cdot)$ uniformly on the closed disc $\{|z|\le R\}$.
--
--   Slices of a jointly continuous family converge locally uniformly as the parameter converges. It is used to pass from a $C^1$ family of planes to $C^1$-convergence of its slices on compact sets (Hryniewicz 2012, Section 7).
--
--   **Formalization Note** Uniform convergence is `TendstoUniformlyOn (fun k z => G (τ k, z)) (fun z => G (t₀, z)) atTop (closedBall 0 R)`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `G` is continuous on `I × ℂ` with `I` open, `t₀ ∈ I` and `τ k → t₀`, then
`G(τ k, ·) → G(t₀, ·)` uniformly on every closed disc `closedBall 0 R`. -/
theorem tendstoUniformlyOn_slice_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (G : ℝ × ℂ → F) (I : Set ℝ) (hI : IsOpen I)
    (hG : ContinuousOn G (I ×ˢ Set.univ)) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (R : ℝ) (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 t₀)) :
    TendstoUniformlyOn (fun k z => G (τ k, z)) (fun z => G (t₀, z)) atTop
      (closedBall (0 : ℂ) R) := by
  sorry

end FiniteEnergyPlane
