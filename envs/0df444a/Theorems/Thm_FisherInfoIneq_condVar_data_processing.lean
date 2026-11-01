-- Prove2me | Theorems.Thm_FisherInfoIneq_condVar_data_processing
-- name    : FisherInfoIneq.condVar_data_processing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:43.141518+00:00
-- url     : https://prove2.me/theorems/89dd8ecb-6590-4af0-bda3-54222d6e7d70
-- title:
--   Eq. (13) — data processing for conditional variance: $W\to X\to Y$ implies $\mathrm{VAR}[W\mid Y]\ge\mathrm{VAR}[W\mid X]$
-- statement:
--   Let $W$ be a real random variable and $X$, $Y$ random variables (with values in arbitrary measurable spaces) on a probability space $(\Omega,P)$ such that $W\to X\to Y$ is a Markov chain, i.e. $W$ and $Y$ are conditionally independent given $X$. Then
--   $$\mathrm{VAR}[W\mid Y]\ \ge\ \mathrm{VAR}[W\mid X],\qquad \mathrm{VAR}[W\mid X]=\mathbb E\big[(W-\mathbb E[W\mid X])^2\big].$$
--
--   Processing the observation can only increase the minimum mean-square error. The paper applies it in (27) to the trivial chain $N_1+N_2\to(X_1,X_2)\to X_1+X_2$.
--
--   **Formalization Note** Both sides are in $[0,\infty]$, so the inequality also covers infinite conditional variances.
--
--   Differences from the source:
--   - generalization: random variables W, X, Y → W real, X and Y with values in arbitrary measurable spaces; reason: the paper itself applies (13) with X = (X₁, X₂) ∈ ℝ²; real-valued X, Y are an instance
--   - encoding: the conditional mean E[W|X] of the paper → the mean of the conditional law condDistrib W X P at X (inside mmse); reason: it is the paper's E[N|X = x] (eq. (33), p.5), the mean of the conditional distribution; it agrees P-a.e. with Mathlib's conditional expectation P[W | σ(X)] whenever the variable is integrable, and unlike condExp it needs no integrability (Mathlib's condExp of a non-integrable function is the junk value 0)
--   - encoding: VAR[W|X] = E[(W − E[W|X])²], a real number → mmse P W X = ∫⁻ ofReal ((W − E[W|X])²) ∂P ∈ [0, ∞]; reason: the expected squared error may be infinite; when it is finite it is the same number
--   - encoding: W → X → Y form a Markov chain → IsMarkovChain P W X Y: P[1_{W∈A} 1_{Y∈B} | σ(X)] = P[1_{W∈A} | σ(X)] · P[1_{Y∈B} | σ(X)] a.s. for all measurable A, B; reason: the conditional independence of W and Y given X, written on generating events because Mathlib's CondIndepFun needs a standard Borel sample space
-- source:
--   Liu–Viswanath, Two Proofs of the Fisher Information Inequality via Data Processing Arguments, arXiv:cs/0604028v1, eq. (13) and the sentence before it, p.3; applied in eq. (27), p.4

import Mathlib
import Definitions.Def_FisherInfoIneq_mmse
import Definitions.Def_FisherInfoIneq_IsMarkovChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FisherInfoIneq

/-- **Display (13): data processing inequality for conditional variance.** Let `W` be a
real random variable and `X`, `Y` random variables (with values in arbitrary measurable
spaces) on a probability space `(Ω, P)` such that `W → X → Y` is a Markov chain. Then
`VAR[W | Y] ≥ VAR[W | X]`, where `VAR[W | X] = E[(W − E[W | X])²]`.

Liu–Viswanath, *Two Proofs of the Fisher Information Inequality via Data Processing Arguments*,
arXiv:cs/0604028v1, eq. (13), p.3; applied in (27), p.4.

**Formalization Note**
1. `X`, `Y` take values in arbitrary measurable spaces (the paper applies (13) with
   `X = (X₁, X₂) ∈ ℝ²`).
2. `VAR` is `mmse`, valued in `ℝ≥0∞`; no square-integrability is assumed.
3. No integrability of `W` is assumed: `mmse` uses the mean of the conditional law of `W` given
   `X = x`; if that law fails to be integrable on a set of positive probability, `VAR = ∞`. -/
theorem condVar_data_processing {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (X : Ω → β) (Y : Ω → γ) (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hM : IsMarkovChain P W X Y) : mmse P W X ≤ mmse P W Y := by sorry

end FisherInfoIneq
