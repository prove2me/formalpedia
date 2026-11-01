-- Prove2me | Theorems.Thm_FisherInfoIneq_fii_smoothed
-- name    : FisherInfoIneq.fii_smoothed
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:33.685514+00:00
-- url     : https://prove2.me/theorems/d8940f4d-5172-4fb6-9606-13d41da2b814
-- title:
--   Eq. (29) — $(a+b)^2J(X_1+X_2)\le a^2J(X_1)+b^2J(X_2)$ for the Gaussian-smoothed variables (corrected: mutual independence)
-- statement:
--   Consider the Bayesian estimation model (22): for $a,b\ge0$ and $t>0$,
--   $$X_1=N_1+\sqrt{at}\,W_1,\qquad X_2=N_2+\sqrt{bt}\,W_2,$$
--   where $W_1,W_2$ are standard Gaussian and $N_1,N_2,W_1,W_2$ are mutually independent real random variables. Then
--   $$(a+b)^2J(X_1+X_2)\le a^2J(X_1)+b^2J(X_2).$$
--
--   This is the Fisher information inequality for the noisy versions $X_1$, $X_2$; the inequality (4) follows by letting $t\downarrow0$.
--
--   **Formalization Note** $J$ takes values in $[0,\infty]$ and the coefficients are nonnegative reals, with $0\cdot\infty=0$. No density, integrability or finiteness of $J$ is assumed for $N_1$, $N_2$.
--
--   Differences from the source:
--   - correction: N₁, N₂, W₁ and W₂ are pairwise independent (model (22), p.4, and the sentence after (28), p.5) → N₁, N₂, W₁, W₂ mutually independent (iIndepFun of the family ![N₁, N₂, W₁, W₂]); reason: (28) is false under pairwise independence: with a = b = t = 1, N₁ ~ N(0,1), U ~ Unif[1,2], W₁, W₂ ~ N(0,1) mutually independent and N₂ = sign(W₁W₂)·U, the four variables are pairwise independent and N₁, N₂ have densities, yet numerically VAR[N₁+N₂|X₁,X₂] ≈ 0.822 while VAR[N₁|X₁] + VAR[N₂|X₂] ≈ 0.999; mutual independence is the minimal correction and is all the proof of (4) needs, since it constructs W₁, W₂ itself
--   - generalization: N₁, N₂ with probability density functions (standing assumption of (4), p.2) → N₁, N₂ arbitrary measurable real random variables; reason: the smoothed variables X_i have densities whenever their noise is nondegenerate, and the inequality holds without a density for N_i; variables with densities are an instance
--   - encoding: J(X) = COV{ρ_X(X)} for X with a density f, ρ_X = f′/f → fisherInfo (P.map X) = ∫ f′²/f ∈ [0, ∞] over an absolutely continuous density f, and +∞ when the law has none; reason: J is valued in [0, ∞] so that infinite Fisher information is representable; every law with an absolutely continuous density gets the classical value, and +∞ otherwise is the standard convention under which the inequality is stated for all densities
--   - reading: COV{ρ_X(X)} → E[ρ_X(X)²]; reason: the score has mean zero (eq. (30), p.5: 'score functions always have zero mean'), so the variance equals the second moment; the paper itself uses J(X) = E[ρ_X²(X)] in (30)
--   - encoding: real coefficients (a + b)², a², b² multiplying J → ENNReal.ofReal ((a + b)²), ENNReal.ofReal (a²), ENNReal.ofReal (b²) in [0, ∞], with 0 · ∞ = 0; reason: J may be +∞ and the page has no finiteness hypothesis; for finite J it is the same inequality, and 0 · ∞ = 0 is the measure-theoretic convention that makes a = 0 or b = 0 read as the inequality without that term
--   - encoding: model (22): X₁ = N₁ + √(at) W₁, X₂ = N₂ + √(bt) W₂, t > 0, W₁, W₂ standard Gaussian, with a, b ≥ 0 from (4) → hypotheses ∀ ω, X₁ ω = N₁ ω + √(a t) W₁ ω and likewise X₂, 0 ≤ a, 0 ≤ b, 0 < t, P.map W_i = gaussianReal 0 1; reason: the same model; gaussianReal 0 1 is the standard Gaussian law
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, model (22), p.4; eq. (29), p.5

import Mathlib
import Definitions.Def_FisherInfoIneq_fisherInfo

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Display (29): the Fisher information inequality for the Gaussian-smoothed variables**
(corrected: `N₁, N₂, W₁, W₂` mutually independent). In the Bayesian estimation model (22),
`X₁ = N₁ + √(at) W₁`, `X₂ = N₂ + √(bt) W₂` with `t > 0`, `a, b ≥ 0`, `W₁, W₂` standard Gaussian and
`N₁, N₂, W₁, W₂` mutually independent,
`(a + b)² J(X₁ + X₂) ≤ a² J(X₁) + b² J(X₂)`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, model (22), p.4, and eq. (29), p.5.

**Formalization Note**
1. **Correction.** The page assumes `N₁, N₂, W₁, W₂` pairwise independent; its derivation of (29)
   passes through (28), which is false under pairwise independence (see `mmse_split`). Mutual
   independence is the minimal correction.
2. `J` is `fisherInfo` of the law, in `ℝ≥0∞`, with `J = +∞` for a law without an absolutely
   continuous density; the coefficients are `ENNReal.ofReal`, and `0 · ∞ = 0`.
3. `N₁, N₂` are not assumed to have densities and no finiteness of `J` is assumed. -/
theorem fii_smoothed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N₁ N₂ W₁ W₂ X₁ X₂ : Ω → ℝ) (hN₁ : Measurable N₁) (hN₂ : Measurable N₂) (hW₁ : Measurable W₁) (hW₂ : Measurable W₂) (hind : iIndepFun ![N₁, N₂, W₁, W₂] P) (hW₁law : P.map W₁ = gaussianReal 0 1) (hW₂law : P.map W₂ = gaussianReal 0 1) (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hX₁ : ∀ ω, X₁ ω = N₁ ω + Real.sqrt (a * t) * W₁ ω) (hX₂ : ∀ ω, X₂ ω = N₂ ω + Real.sqrt (b * t) * W₂ ω) : ENNReal.ofReal ((a + b) ^ 2) * fisherInfo (P.map (X₁ + X₂)) ≤ ENNReal.ofReal (a ^ 2) * fisherInfo (P.map X₁) + ENNReal.ofReal (b ^ 2) * fisherInfo (P.map X₂) := by sorry

end FisherInfoIneq
