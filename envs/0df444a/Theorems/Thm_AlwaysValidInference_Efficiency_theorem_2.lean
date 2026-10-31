-- Prove2me | Theorems.Thm_AlwaysValidInference_Efficiency_theorem_2
-- name    : AlwaysValidInference.Efficiency.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:41:30.107897+00:00
-- url     : https://prove2.me/theorems/8ce95845-7175-4cf8-91da-4b8fc96e5ee7
-- title:
--   Theorem 2 — first-order efficiency of every mSPRT
-- statement:
--   Fix any model satisfying Sections 3 and 5.2 and suppose $\psi''$ is absolutely continuous on its parameter interval and finite on an open neighborhood of the null $\theta_0$. Let $H$ be any fixed probability mixing distribution with everywhere continuous positive density. For every $\alpha\in(0,1)$ and positive integer $M$, use the actual truncated mSPRT, and take the infimum over every natural-filtration decision rule with $T\le M$ almost surely, Type I error at most $\alpha$, and power at least that of the truncated mSPRT at every alternative. Then, with the parameter infimum still inside the limit,
--   $$\phi(M,\alpha)=\inf_{(T,\delta)\ \mathrm{feasible}}\inf_{\theta\in\Theta\setminus\{\theta_0\}}\frac{E_\theta[T]/M}{E_\theta[\min(T^H(\alpha),M)]/M}\longrightarrow 1$$
--   whenever $\alpha\to0$, $M\to\infty$, and $M=O(\log(1/\alpha))$. Equivalently this holds along every sequence obeying those conditions. Neither the mixture nor the competitor is allowed to depend on the unknown parameter; competitors may be chosen separately at each $M,\alpha$.
--
--   The exact limiting constant is one. The claim includes all paths with $M/\log(1/\alpha)\to0$ and arbitrarily close alternatives to the null. The proof gaps recorded in I1 and I2 do not change this printed target.
--
--   Differences from the source:
--   - generalization: density f₀(x) exp(θx − ψ(θ)) with respect to Lebesgue measure → exp(θx − ψ(θ)) with respect to an arbitrary reference measure; reason: taking reference = f₀ dx recovers every source family without any added assumption
--   - reading: equation (7) writes the density quotient at the sample mean → the exponential likelihood ratio after cancelling the common carrier; reason: this is the intended likelihood ratio, agreeing wherever the quotient is defined; I3 records a source-admissible support where the printed quotient is 0/0
--   - encoding: observations indexed from one and positive integer stopping times with possible infinity → observation index zero is X₁; times lie in ℕ∞ with positivity imposed; reason: the first n coordinates are exactly the first n samples and the empty crossing set remains infinity
--   - encoding: all stopping-time binary decision rules for the observation filtration → time and decision functions constrained by the generated history sigma algebras and their stopped events; reason: the event characterization is exactly stopped measurability; no external randomization or unknown-parameter dependence is introduced
--   - encoding: real-valued normalized expectations and two infima over the feasible classes → nonnegative extended expectations and nested ENNReal infima; reason: bounded positive horizons make the source quantities finite and denominators positive; extended values avoid arbitrary defaults on invalid or empty inputs
--   - encoding: ψ second derivative is absolutely continuous and finite on an open interval around θ₀ → global epsilon-delta absolute continuity on the parameter interval; actual second differentiability with real derivative throughout the open domain containing θ₀; reason: this retains global absolute continuity and the finite-neighborhood condition without requiring another smoothness class
--   - encoding: joint limit α → 0, M → infinity with M = O(log(1/α)) → every sequence of valid α and positive integer M satisfying these limits and an eventual finite positive big-O constant; reason: the first-countable joint domain admits this equivalent sequential formulation; no positive lower bound on M/log(1/α) is imposed
-- source:
--   Johari, Pekelis and Walsh, Always Valid Inference: Continuous Monitoring of A/B Tests, arXiv:1512.04922v3 (2019), https://arxiv.org/abs/1512.04922v3, Theorem 2 and Definition 3, p. 21 (PDF page = printed page).

import Definitions.Def_AlwaysValidInference_Efficiency_Efficiency

open Filter Set
open scoped Topology

namespace AlwaysValidInference.Efficiency

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (hregular : E.Regular) (H : MixingDistribution E.family.domain)
    (α : ℕ → ℝ) (M : ℕ → ℕ)
    (hα : ∀ k, α k ∈ Ioo (0 : ℝ) 1) (hM : ∀ k, 1 ≤ M k)
    (hα_zero : Tendsto α atTop (𝓝 0)) (hM_top : Tendsto M atTop atTop)
    (hregime : ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
      (M k : ℝ) ≤ C * Real.log (1 / α k)) :
    Tendsto (fun k => efficiency E H (α k) (M k)) atTop (𝓝 1) := by sorry

end AlwaysValidInference.Efficiency
