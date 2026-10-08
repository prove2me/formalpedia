-- Prove2me | Theorems.Thm_AIMInventory_Known_lemma_12
-- name    : AIMInventory.Known.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:28.258766+00:00
-- url     : https://prove2.me/theorems/cc2efb49-f783-47b5-bd6a-1dba8a425a43
-- title:
--   Lemma 12 — for i.i.d. mean-zero X_i, E[(ΣX_i)⁴] ≤ 3n²EX₁⁴ and E[(ΣX_i)⁶] ≤ 21n³EX₁⁶
-- statement:
--   Let $X_1, X_2, \dots$ be independent and identically distributed real random variables with $E X_1 = 0$, and let $n \ge 1$. Then
--
--   1. if $E X_1^4 < \infty$,
--   $$E\Big[\Big(\sum_{i=1}^n X_i\Big)^4\Big] \le 3n^2\, E X_1^4;$$
--   2. if $E X_1^6 < \infty$,
--   $$E\Big[\Big(\sum_{i=1}^n X_i\Big)^6\Big] \le 21n^3\, E X_1^6.$$
--
--   The sixth-moment bound, with Markov's inequality, gives the tail $P\{|J_1(\theta)| \ge \ell\} = O(\ell^{-3})$ behind Proposition 4 (i).
--
--   **Formalization Note** The sequence is indexed from $0$ in Lean ($X_1$ is `X 0`, and the sum runs over `Finset.range n`). Independence is mutual independence (`iIndepFun`), identical distribution is `IdentDistrib` with `X 0`, and finiteness of the moment is `MemLp` of order $4$ or $6$; these make $E X_1 = 0$ a statement about an integrable variable.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 17, Lemma 12 (Appendix B)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace AIMInventory.Known

/-- Lemma 12, p. 17: for i.i.d. real random variables with mean zero,
`E[(Σ_{i=1}^n X_i)^4] ≤ 3n² E[X_1^4]` when `E[X_1^4] < ∞`, and
`E[(Σ_{i=1}^n X_i)^6] ≤ 21n³ E[X_1^6]` when `E[X_1^6] < ∞`. -/
theorem lemma_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (n : ℕ) (hn : 1 ≤ n) :
    (MemLp (X 0) 4 μ →
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂μ ≤ 3 * (n : ℝ) ^ 2 * ∫ ω, X 0 ω ^ 4 ∂μ) ∧
    (MemLp (X 0) 6 μ →
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 6 ∂μ ≤ 21 * (n : ℝ) ^ 3 * ∫ ω, X 0 ω ^ 6 ∂μ) := by sorry

end AIMInventory.Known
