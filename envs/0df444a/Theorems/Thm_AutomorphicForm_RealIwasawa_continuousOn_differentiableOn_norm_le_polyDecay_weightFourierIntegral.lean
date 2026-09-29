-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
-- name    : AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/dd42a10c-dd69-57a2-abbc-ec3425a4629b
-- title:
--   Weight-k real Whittaker integral: continuity, holomorphy, rapid decay
-- statement:
--   Fix an integer $k$, and for $w \in \mathbb{C}$, $t \in \mathbb{R}$ let
--   $$j(w,t) \;=\; \int_{\mathbb{R}} \Big(\frac{x - i}{\sqrt{1+x^{2}}}\Big)^{k} \,(1+x^{2})^{-w}\, e^{-2\pi i t x}\, dx,$$
--   the Bochner integral against Lebesgue measure of the product of the $k$-th integer power of $(x-i)/\sqrt{1+x^{2}}$, the complex power $(1+x^{2})^{-w}$, and $\exp(-2\pi i t x\cdot i/i)$, i.e. $\exp(-(2\pi t x)i)$; no integrability hypothesis is imposed, the integral being interpreted in Lean's convention. The assertion is the conjunction of three statements. First, the uncurried map $(w,t) \mapsto j(w,t)$ is continuous on the product of the half-plane $\{w : \tfrac12 < \operatorname{Re} w\}$ with all of $\mathbb{R}$. Second, for every real $t$ the function $w \mapsto j(w,t)$ is complex differentiable on that half-plane. Third, for every compact set $K \subseteq \mathbb{C}$ contained in the half-plane and every natural number $N$ there is a real constant $C > 0$ such that $\lVert j(w,t)\rVert \le C\,(1+|t|)^{-N}$ for all $w \in K$ and all $t \in \mathbb{R}$, the exponent being a real power.
--
--   This is the weight-$k$ archimedean Whittaker (Jacquet) integral for $\mathrm{GL}_2(\mathbb{R})$ on its half-plane of absolute convergence, together with the uniform rapid decay in the additive variable. It feeds the construction of the entire continuation of the real-place Fourier coefficient integrals and the attendant growth bounds on vertical strips, which are used in the archimedean analysis of Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ContinuousOn (fun p : ℂ × ℝ => j p.1 p.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => j w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖j w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) := by sorry
