-- Prove2me | Theorems.Thm_FisherInfoIneq_lemma_1
-- name    : FisherInfoIneq.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:28.869772+00:00
-- url     : https://prove2.me/theorems/521b2bc1-fda9-420d-9d25-007b386e2dc5
-- title:
--   Lemma 1 — $J(N+W)=\frac1{\sigma^4}\{\sigma^2-\mathrm{VAR}[N\mid N+W]\}$ for Gaussian $W$
-- statement:
--   Let $N$ and $W$ be independent real random variables on a probability space $(\Omega,P)$, where $W$ is Gaussian with mean $0$ and variance $\sigma^2>0$. Then $\mathrm{VAR}[N\mid N+W]\le\sigma^2$ and
--   $$J(N+W)=\frac{1}{\sigma^4}\Big\{\sigma^2-\mathrm{VAR}[N\mid N+W]\Big\}.$$
--   Here $J$ is the Fisher information and $\mathrm{VAR}[N\mid X]=\mathbb E[(N-\mathbb E[N\mid X])^2]$.
--
--   The lemma links Fisher information to minimum mean-square estimation in additive Gaussian noise; applied to the smoothed model (22) it gives (24)–(26). It is equivalent, through the de Bruijn identity, to the I-MMSE relation of Guo, Shamai and Verdú.
--
--   **Formalization Note** Both sides are computed in $[0,\infty]$; the first conclusion $\mathrm{VAR}[N\mid N+W]\le\sigma^2$ (a consequence of (23), since $J\ge0$) makes the subtraction the real one. The Gaussian law is Mathlib's `gaussianReal 0 v` with $v=\sigma^2$, so $\sigma^4=v^2$.
--
--   Differences from the source:
--   - encoding: W Gaussian with zero mean and variance σ² → P.map W = gaussianReal 0 v with v ≠ 0, σ² = v; reason: σ = 0 makes 1/σ⁴ undefined; gaussianReal takes the variance
--   - encoding: the conditional mean E[N|X = x] of the paper → the mean of the conditional law condDistrib N (N + W) P at x (inside mmse); reason: it is the paper's E[N|X = x] (eq. (33), p.5), the mean of the conditional distribution; it agrees P-a.e. with Mathlib's conditional expectation P[N | σ(N + W)] whenever the variable is integrable, and unlike condExp it needs no integrability (Mathlib's condExp of a non-integrable function is the junk value 0); the conditional law of N given N + W has Gaussian tails, so no integrability of N is needed
--   - encoding: J(N + W) = (1/σ⁴){σ² − VAR[N|N+W]} as real numbers → VAR[N|N+W] ≤ σ² ∧ J(N+W) = (1/σ⁴)·(σ² − VAR[N|N+W]) in [0, ∞]; reason: J and VAR are valued in [0, ∞]; the first conjunct, implied by (23) since J ≥ 0, makes the truncated subtraction in [0, ∞] the real one
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, Lemma 1, eq. (23), p.4; proof in Appendix A, eqs. (30)–(40), p.5

import Mathlib
import Definitions.Def_FisherInfoIneq_fisherInfo
import Definitions.Def_FisherInfoIneq_mmse

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FisherInfoIneq

/-- **Lemma 1: Fisher information of `N + W` through the MMSE.** Let `N` and `W` be independent
real random variables on a probability space `(Ω, P)`, with `W` Gaussian of mean `0` and variance
`σ² = v > 0`. Then `VAR[N | N + W] ≤ σ²` and
`J(N + W) = (1/σ⁴) {σ² − VAR[N | N + W]}`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, Lemma 1, eq. (23), p.4; proof in Appendix A, eqs. (30)–(40), p.5.

**Formalization Note**
1. `gaussianReal 0 v` takes the variance `v = σ²`, so `σ⁴ = v²`. `v ≠ 0` excludes `σ = 0`, where
   `1/σ⁴` is undefined.
2. `VAR[N | N + W] = mmse P N (N + W) = E[(N − E[N | N + W])²]` and `J` are in `ℝ≥0∞`; the first
   conjunct `VAR ≤ σ²` (which follows from (23) because `J ≥ 0`) makes the truncated subtraction
   `σ² − VAR` in `ℝ≥0∞` the real one.
3. No integrability of `N` is assumed: `mmse` uses the mean of the conditional law of `N` given
   `N + W = x` (the paper's `E[N|X = x]`, eq. (33)), which has Gaussian tails for every `N`; the
   paper applies the lemma in (24)–(26) to arbitrary `N₁`, `N₂`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N W : Ω → ℝ) (hN : Measurable N) (hW : Measurable W) (hind : IndepFun N W P) (v : ℝ≥0) (hv : v ≠ 0) (hWlaw : P.map W = gaussianReal 0 v) : mmse P N (N + W) ≤ (v : ℝ≥0∞) ∧ fisherInfo (P.map (N + W)) = (1 / (v : ℝ≥0∞) ^ 2) * ((v : ℝ≥0∞) - mmse P N (N + W)) := by sorry

end FisherInfoIneq
