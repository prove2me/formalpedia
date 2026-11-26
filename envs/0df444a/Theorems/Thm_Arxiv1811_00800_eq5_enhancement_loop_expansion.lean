-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq5_enhancement_loop_expansion
-- name    : Arxiv1811_00800.eq5_enhancement_loop_expansion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:45:06.013816+00:00
-- url     : https://prove2.me/theorems/4770dd7a-afbc-5f32-b03e-b0285cf699a5
-- title:
--   Eq. (5): the enhancement factor is $\sum_{n\in\mathbb N}p_n[1+\cos(4\pi n\alpha)]$
-- statement:
--   Let $\lambda>0$, $c>0$, $\Gamma\in\mathbb{R}$ and $\alpha=\Gamma/(\lambda c)$. Let $P$ be a probability measure on an ensemble of closed Lipschitz paths $\gamma_\omega$, none passing through the filament at the origin, such that the number of loops $\omega\mapsto n(\gamma_\omega,0)$ is measurable. Let $p_n$, $n\in\mathbb{N}$, be the probability that a path makes $n$ loops around the filament (in either direction). Then the enhancement factor of the flow $v=\frac{\Gamma}{2\pi r}u_\theta$, the mean of $1+\cos\Delta\varphi$ over the ensemble, is
--
--   $$E(\alpha)=\sum_{n\in\mathbb{N}}p_n\left[1+\cos(4\pi n\alpha)\right].$$
--
--   **Formalization Note** The paper sums over $n\in\mathbb{N}$ while the $n$ of Eq. (4) is a signed integer. Since cosine is even, the sum is read with $n$ the number of loops regardless of direction, $p_n=P(|n(\gamma_\omega,0)|=n)$. Neglecting scattering by the vortex core, as the paper does, is built in: the dephasing is that of Eq. (4). The ensemble of paths is an abstract probability space.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c007; main text, after Eq. (4), Eq. (5), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq5_enhancement_loop_expansion {W : Type*} [MeasurableSpace W] (P : Measure W)
    [IsProbabilityMeasure P] (Gam lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c) (γ : W → ℝ → ℂ)
    (hγ : ∀ ω, IsClosedPath (γ ω)) (h0 : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ ω t ≠ 0)
    (hmeas : Measurable fun ω => windingNumber (γ ω) 0) :
    enhancementFactor P (fun ω => phaseDiff lam c (vortexField Gam) (γ ω)) =
      loopEnhancement (loopNumberLaw P γ) (abParam Gam lam c) := by sorry

end Arxiv1811_00800
