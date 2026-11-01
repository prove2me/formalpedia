-- Prove2me | Theorems.Thm_FisherInfoIneq_fisherInfo_gaussian_smoothing_tendsto
-- name    : FisherInfoIneq.fisherInfo_gaussian_smoothing_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:38.296072+00:00
-- url     : https://prove2.me/theorems/14aae3e2-109f-4455-b892-2f8ead7f0509
-- title:
--   Sentence after (29) — $J(N+\sqrt{s}\,W)\to J(N)$ as $s\downarrow0$
-- statement:
--   Let $N$ be a real random variable with a probability density function and $W$ a standard Gaussian random variable independent of $N$, on a probability space $(\Omega,P)$. Then
--   $$\lim_{s\downarrow0}J\big(N+\sqrt{s}\,W\big)=J(N)\quad\text{in }[0,\infty],$$
--   including the case $J(N)=\infty$.
--
--   The page asserts that $J(X_1)$, $J(X_2)$ and $J(X_1+X_2)$ of model (22) approach $J(N_1)$, $J(N_2)$ and $J(N_1+N_2)$ as $t\downarrow0$. Each is an instance: $X_1=N_1+\sqrt{s}\,W_1$ with $s=at$ (for $a=0$, $X_1=N_1$), likewise $X_2$, and $X_1+X_2=(N_1+N_2)+\sqrt{s}\,W$ with $s=(a+b)t$ and the standard Gaussian $W=(\sqrt a\,W_1+\sqrt b\,W_2)/\sqrt{a+b}$, which is independent of $N_1+N_2$. This limit carries (29) to (4).
--
--   **Formalization Note** The limit is taken along $s\to0^+$ in the order topology of $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: J(X₁), J(X₂), J(X₁ + X₂) of model (22) approach J(N₁), J(N₂), J(N₁ + N₂) as t ↓ 0 → for every N with a density and every standard Gaussian W independent of N, J(N + √s W) → J(N) as s ↓ 0; reason: the three limits on the page are instances (s = at, s = bt, s = (a+b)t with W = (√a W₁ + √b W₂)/√(a+b)); the general statement is the one the three share
--   - encoding: 'approach … in the limit' → Tendsto … (𝓝[>] 0) (𝓝 (fisherInfo (P.map N))) in [0, ∞]; reason: J may be +∞; convergence in [0, ∞] is the meaning of 'approach' that covers that case and agrees with real convergence for finite values
--   - encoding: J(X) = COV{ρ_X(X)} for X with a density f, ρ_X = f′/f → fisherInfo (P.map X) = ∫ f′²/f ∈ [0, ∞] over an absolutely continuous density f, and +∞ when the law has none; reason: J is valued in [0, ∞] so that infinite Fisher information is representable; every law with an absolutely continuous density gets the classical value, and +∞ otherwise is the standard convention under which the inequality is stated for all densities
--   - reading: COV{ρ_X(X)} → E[ρ_X(X)²]; reason: the score has mean zero (eq. (30), p.5: 'score functions always have zero mean'), so the variance equals the second moment; the paper itself uses J(X) = E[ρ_X²(X)] in (30)
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, the sentence after eq. (29), p.5

import Mathlib
import Definitions.Def_FisherInfoIneq_fisherInfo

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace FisherInfoIneq

/-- **Sentence after (29): Gaussian smoothing is continuous in `J` as the noise vanishes.** Let
`N` be a real random variable with a probability density function, and `W` a standard Gaussian
random variable independent of `N`, on a probability space `(Ω, P)`. Then
`J(N + √s W) → J(N)` as `s ↓ 0`, in `[0, ∞]` (including the case `J(N) = ∞`).

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, the sentence after eq. (29), p.5: "Note that J(X₁), J(X₂) and J(X₁ + X₂)
approach J(N₁), J(N₂) and J(N₁ + N₂), respectively, in the limit as t ↓ 0."

**Formalization Note**
1. The page's three limits are instances: `X₁ = N₁ + √(at) W₁` with `s = at` (`a > 0`; for
   `a = 0`, `X₁ = N₁`), likewise `X₂`, and `X₁ + X₂ = (N₁ + N₂) + √((a+b)t) W` with the standard
   Gaussian `W = (√a W₁ + √b W₂)/√(a + b)`, independent of `N₁ + N₂`.
2. `J` is `fisherInfo` of the law, in `ℝ≥0∞`; the limit is taken in the order topology of `[0, ∞]`
   along `s → 0⁺` (`𝓝[>] 0`). -/
theorem fisherInfo_gaussian_smoothing_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N W : Ω → ℝ) (hN : Measurable N) (hW : Measurable W) (hind : IndepFun N W P) (hWlaw : P.map W = gaussianReal 0 1) (hpdf : HasPDF N P) : Tendsto (fun s : ℝ => fisherInfo (P.map (fun ω => N ω + Real.sqrt s * W ω))) (𝓝[>] 0) (𝓝 (fisherInfo (P.map N))) := by sorry

end FisherInfoIneq
