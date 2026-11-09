-- Prove2me | Theorems.Thm_BosonicLearn_theorem_5
-- name    : BosonicLearn.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:42:13.980081+00:00
-- url     : https://prove2.me/theorems/eba16fe3-c2fb-46dd-8919-e5d4235c83b7
-- title:
--   Theorem 5 — adaptive single-copy learning of passive states with $\Sigma\succeq(\tfrac12+\nu)I$, $\tfrac1n\le\nu\le1$, needs $\Omega(n^2/(\nu\varepsilon^2))$ copies
-- statement:
--   There are $\varepsilon_0,c>0$ and $n_0$ such that for every $n\ge n_0$, every $\nu\in[1/n,1]$ and every $\varepsilon\in(0,\varepsilon_0)$: if an adaptive single-copy scheme on $N$ copies, with any outcome space and any (randomized) estimator, learns every $n$-mode passive Gaussian state with $\Sigma\succeq(\tfrac12+\nu)I$ to trace distance $\varepsilon$ with probability at least $2/3$, then
--
--   $$N\ge c\,\frac{n^2}{\nu\varepsilon^2}.$$
--
--   For $\nu=1/n$ this is $\Omega(n^3/\varepsilon^2)$ and for $\nu=1$ the classical $\Omega(n^2/\varepsilon^2)$; heterodyne detection attains it (Theorem 8).
--
--   Differences from the source:
--   - reading: "for any sufficiently small ε", N = Ω(n²/(νε²)) → ∃ ε₀, c > 0 and n₀, uniform in ν and ε, with n ≥ n₀; reason: the asymptotic meaning of Ω; it is what the proof of Theorem 3 uses
--   - encoding: "single-copy measurements", possibly adaptive, with an estimator → adaptive schemes of POVMs with an arbitrary measurable outcome space, round laws measurable in the earlier outcomes, and a Markov-kernel estimator to density operators; reason: the paper's model (§1.1 p. 5, §4 p. 19, §5.1 p. 30); measurability makes the transcript a random variable
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 5, p. 29

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_IsPassive
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Theorem 5 (Tight single-copy lower bound for all-temperature Gaussian states).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 5, p. 29: "For any sufficiently small ε > 0, any single-copy adaptive scheme that can learn any
n-mode passive Gaussian state, given the promise that Σ ≥ (1/2 + ν)I for any 1/n ≤ ν ≤ 1, to trace distance
precision ε with at least 2/3 probability requires at least N = Ω(n²/(νε²)) copies."

There are `ε₀, c > 0` and `n₀` such that for every `n ≥ n₀`, `ν ∈ [1/n, 1]`, `ε ∈ (0, ε₀)`, every `N`, every adaptive
single-copy scheme on `N` copies with any measurable outcome space and every (randomized) estimator: if every passive
Gaussian state with `Σ ⪰ (½ + ν)I` is learned to trace distance `ε` with probability at least `2/3`, then
`N ≥ c n²/(νε²)`.

**Formalization Note.** `Ω(·)` is read with a universal constant and a threshold `n₀` (asymptotic in `n`), uniform in
`ν` and `ε`. The class is the passive states of the promise class. -/
theorem theorem_5 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
        (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
        (∀ ρ ∈ promiseClass n ν, IsPassive ρ →
          ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
        c * ((n : ℝ) ^ 2 / (ν * ε ^ 2)) ≤ N := by sorry

end BosonicLearn
