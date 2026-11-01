-- Prove2me | Theorems.Thm_FisherInfoIneq_mmse_split
-- name    : FisherInfoIneq.mmse_split
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:43.54882+00:00
-- url     : https://prove2.me/theorems/78028748-828d-4115-979a-a66a4d5d20a8
-- title:
--   Eq. (28) — $\mathrm{VAR}[N_1+N_2\mid X_1,X_2]=\mathrm{VAR}[N_1\mid X_1]+\mathrm{VAR}[N_2\mid X_2]$ (corrected: $N_1,N_2,W_1,W_2$ mutually independent)
-- statement:
--   Consider the Bayesian estimation model (22): for $a,b\ge0$ and $t>0$,
--   $$X_1=N_1+\sqrt{at}\,W_1,\qquad X_2=N_2+\sqrt{bt}\,W_2,$$
--   where $W_1,W_2$ are standard Gaussian, $N_1,N_2$ are real random variables, and $N_1,N_2,W_1,W_2$ are mutually independent. Then
--   $$\mathrm{VAR}[N_1+N_2\mid X_1,X_2]=\mathrm{VAR}[N_1\mid X_1]+\mathrm{VAR}[N_2\mid X_2].$$
--
--   Estimating the sum from both observations splits into two independent estimation problems. Combined with (27) and Lemma 1 it gives the smoothed inequality (29).
--
--   **Formalization Note** The page assumes only pairwise independence, under which the identity is false (see the correction below). Conditional variances are in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: N₁, N₂, W₁ and W₂ are pairwise independent (model (22), p.4, and the sentence after (28), p.5) → N₁, N₂, W₁, W₂ mutually independent (iIndepFun of the family ![N₁, N₂, W₁, W₂]); reason: (28) is false under pairwise independence: with a = b = t = 1, N₁ ~ N(0,1), U ~ Unif[1,2], W₁, W₂ ~ N(0,1) mutually independent and N₂ = sign(W₁W₂)·U, the four variables are pairwise independent and N₁, N₂ have densities, yet numerically VAR[N₁+N₂|X₁,X₂] ≈ 0.822 while VAR[N₁|X₁] + VAR[N₂|X₂] ≈ 0.999; mutual independence is the minimal correction and is all the proof of (4) needs, since it constructs W₁, W₂ itself
--   - encoding: the conditional means E[·|X₁], E[·|X₂], E[·|X₁, X₂] of the paper → means of the conditional laws condDistrib (inside mmse); reason: it is the paper's E[N|X = x] (eq. (33), p.5), the mean of the conditional distribution; it agrees P-a.e. with Mathlib's conditional expectation P[W | σ(X)] whenever the variable is integrable, and unlike condExp it needs no integrability (Mathlib's condExp of a non-integrable function is the junk value 0); in model (22) the conditional laws given X_i have Gaussian tails (or are Dirac when a = 0), so no integrability of N₁, N₂ is needed
--   - encoding: VAR[W|X] = E[(W − E[W|X])²], a real number → mmse P W X = ∫⁻ ofReal ((W − E[W|X])²) ∂P ∈ [0, ∞]; reason: the expected squared error may be infinite; when it is finite it is the same number
--   - encoding: model (22): X₁ = N₁ + √(at) W₁, X₂ = N₂ + √(bt) W₂, t > 0, W₁, W₂ standard Gaussian, with a, b ≥ 0 from (4) → hypotheses ∀ ω, X₁ ω = N₁ ω + √(a t) W₁ ω and likewise X₂, 0 ≤ a, 0 ≤ b, 0 < t, P.map W_i = gaussianReal 0 1; reason: the same model; gaussianReal 0 1 is the standard Gaussian law
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, model (22), p.4; eq. (28), p.4, and the sentence after it, p.5

import Mathlib
import Definitions.Def_FisherInfoIneq_mmse

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Display (28): the conditional variance splits** (corrected: `N₁, N₂, W₁, W₂` mutually
independent). In the Bayesian estimation model (22), `X₁ = N₁ + √(at) W₁`, `X₂ = N₂ + √(bt) W₂`
with `t > 0`, `a, b ≥ 0`, `W₁, W₂` standard Gaussian and `N₁, N₂, W₁, W₂` mutually independent,
`VAR[N₁ + N₂ | X₁, X₂] = VAR[N₁ | X₁] + VAR[N₂ | X₂]`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, model (22) and eq. (28), pp.4–5: "where the last equality follows from the
fact that N₁, N₂, W₁ and W₂ are pairwise independent".

**Formalization Note**
1. **Correction.** The page assumes *pairwise* independence, under which (28) is false: with
   `a = b = t = 1`, `N₁ ~ N(0, 1)`, `U ~ Unif[1, 2]`, `W₁, W₂ ~ N(0, 1)` mutually independent and
   `N₂ = sign(W₁W₂)·U`, the four variables are pairwise independent, yet numerically
   `VAR[N₁ + N₂ | X₁, X₂] ≈ 0.822` while `VAR[N₁ | X₁] + VAR[N₂ | X₂] ≈ 0.999`. Mutual
   independence (`iIndepFun` of the family `![N₁, N₂, W₁, W₂]`) is the minimal correction, and it
   is what the proof of the inequality (4) uses.
2. `VAR[N₁ + N₂ | X₁, X₂]` conditions on the pair `(X₁, X₂)`; `VAR` is `mmse`, valued in `ℝ≥0∞`.
3. No integrability of `N₁`, `N₂` is assumed: `mmse` uses the mean of the conditional law, as the
   paper's `E[N|X = x]`, and the paper applies (28) to arbitrary `N₁`, `N₂` with densities.
4. `gaussianReal 0 1` is the standard Gaussian law. -/
theorem mmse_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N₁ N₂ W₁ W₂ X₁ X₂ : Ω → ℝ) (hN₁ : Measurable N₁) (hN₂ : Measurable N₂) (hW₁ : Measurable W₁) (hW₂ : Measurable W₂) (hind : iIndepFun ![N₁, N₂, W₁, W₂] P) (hW₁law : P.map W₁ = gaussianReal 0 1) (hW₂law : P.map W₂ = gaussianReal 0 1) (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hX₁ : ∀ ω, X₁ ω = N₁ ω + Real.sqrt (a * t) * W₁ ω) (hX₂ : ∀ ω, X₂ ω = N₂ ω + Real.sqrt (b * t) * W₂ ω) : mmse P (N₁ + N₂) (fun ω => (X₁ ω, X₂ ω)) = mmse P N₁ X₁ + mmse P N₂ X₂ := by sorry

end FisherInfoIneq
