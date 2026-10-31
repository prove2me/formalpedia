-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_5
-- name    : DeltaSLearning.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:06.123006+00:00
-- url     : https://prove2.me/theorems/ec037fc1-5c9d-4220-8c29-8fb170eff4c6
-- title:
--   Lemma 5 — capped queue: $\mathbb E[\sum_nZ_n]=O(\sqrt N)$
-- statement:
--   Let the departures $D_1,D_2,\dots$ be i.i.d. positive random variables. For each horizon $N$ let the arrivals $A_1,\dots,A_N$ be nonnegative and integrable, with $A_n$ independent of $(D_n,\dots,D_N)$, and let
--   $$Z_1=0,\qquad Z_{n+1}=\mathrm{Proj}_{[0,\beta]}(Z_n+A_n-D_n),$$
--   with $\beta\ge0$. If there is $C_1$ with $\mathbb E[\sum_{n=1}^NA_n]\le C_1\sqrt N$ for every $N$, then there is $C_2$ with
--   $$\mathbb E\Bigl[\sum_{n=1}^NZ_n\Bigr]\le C_2\sqrt N\qquad\text{for every }N .$$
--
--   In Proposition 3, $Z_n$ dominates the excess of the implemented target over the leader's target.
--
--   Differences from the source:
--   - reading: E[Σ A_n] = O(√N) ⇒ E[Σ Z_n] = O(√N) for a queue over horizon N → for a family of arrivals indexed by N: ∃ C₁ ∀ N in the hypothesis, ∃ C₂ ∀ N in the conclusion; reason: an O(·) statement is about a family; the arrivals may depend on N
--   - reading: the departure process {D_n}_n → one sequence of departures for all horizons N; reason: the departures are a process indexed by n alone
--   - reading: arrival process {A_n}_n → arrivals are nonnegative and integrable; reason: arrivals in a queue are nonnegative; E[Σ A_n] presupposes integrability
--   - encoding: i.i.d. positive random variables → measurable, iIndepFun, IdentDistrib, and positive almost surely; reason: same set of laws
--   - encoding: indices n = 1, …, N → 0-based indices k = 0, …, N − 1; reason: Lean indexing; no instance changes
--   - encoding: E[Σ_n Z_n] (finiteness presupposed) → integrability of Σ_n Z_n stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 5, p.26; proof pp.42–43

import Mathlib
import Definitions.Def_DeltaSLearning_capQueue

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Lemma 5** (bound on total waiting time). Let the departures `D_1, D_2, …` be i.i.d. positive
random variables. For each horizon `N` let the arrivals `A_1, …, A_N` be nonnegative, with
`A_n` independent of `(D_n, …, D_N)`, and let `Z_1 = 0`, `Z_{n+1} = Proj_{[0,β]}(Z_n + A_n - D_n)`.
If `E[Σ_{n=1}^N A_n] = O(√N)`, then `E[Σ_{n=1}^N Z_n] = O(√N)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 5, p.26; proof pp.42–43.

**Formalization Note** 0-based indices (`A N k`, `Dep k` are the paper's `A_{k+1}`, `D_{k+1}` at
horizon `N`). The `O(·)` is read over the family indexed by `N`: `∃ C₁ ∀ N` in the hypothesis,
`∃ C₂ ∀ N` in the conclusion. The arrivals may depend on `N`, the departure law does not.
"Arrivals" are nonnegative; their integrability is what `E[Σ A_n]` presupposes. Integrability of
`Σ Z_n` is stated as a conclusion. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℝ) (hβ : 0 ≤ β) (Dep : ℕ → Ω → ℝ) (hDm : ∀ k, Measurable (Dep k))
    (hDind : iIndepFun Dep P) (hDid : ∀ k, IdentDistrib (Dep k) (Dep 0) P P)
    (hDpos : ∀ k, ∀ᵐ ω ∂P, 0 < Dep k ω)
    (A : ℕ → ℕ → Ω → ℝ) (hA₀ : ∀ N k ω, 0 ≤ A N k ω) (hAint : ∀ N k, Integrable (A N k) P)
    (hAind : ∀ N k, k < N → IndepFun (A N k) (fun ω (i : Finset.Ico k N) => Dep i ω) P)
    (hA : ∃ C₁ : ℝ, ∀ N : ℕ, ∫ ω, ∑ k ∈ Finset.range N, A N k ω ∂P ≤ C₁ * Real.sqrt N) :
    ∃ C₂ : ℝ, ∀ N : ℕ,
      Integrable (fun ω => ∑ k ∈ Finset.range N,
        capQueue β (fun k => A N k ω) (fun k => Dep k ω) k) P ∧
      ∫ ω, ∑ k ∈ Finset.range N, capQueue β (fun k => A N k ω) (fun k => Dep k ω) k ∂P
        ≤ C₂ * Real.sqrt N := by sorry

end DeltaSLearning
