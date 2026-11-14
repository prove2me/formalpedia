-- Prove2me | Theorems.Thm_BosonicLearn_corollary_19
-- name    : BosonicLearn.corollary_19
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:35:55.433916+00:00
-- url     : https://prove2.me/theorems/7c42caea-22f5-4e2c-af0a-01125a73637e
-- title:
--   Corollary 19 — heterodyne learns $\rho(\mu,\Sigma)$ with $O(\frac{n^2}{\epsilon^2}\min\{n,1+1/\nu\})$ copies
-- statement:
--   For every failure probability $\delta\in(0,1)$ there is $C_\delta>0$ such that for every $n$, $\nu>0$ and $\epsilon>0$ there are
--
--   $$N\le C_\delta\,\frac{n^2}{\epsilon^2}\min\Big\{n,\,1+\frac1\nu\Big\}$$
--
--   and a non-adaptive protocol of $N$ independent heterodyne measurements that learns every $n$-mode Gaussian state with $\Sigma\succeq(\tfrac12+\nu)I$ to trace distance $\epsilon$ with probability at least $1-\delta$.
--
--   It is the upper-bound half of Theorem 3: the cost interpolates between $n^3/\epsilon^2$ for cold states and $n^2/\epsilon^2$ for warm states.
--
--   Differences from the source:
--   - reading: "for constant failure probability" → for every δ ∈ (0, 1), the constant depending on δ; reason: the proof of Theorem 3 uses δ = 1/3
--   - encoding: O(·) and "there is a … protocol" → ∃ C > 0 before every other variable; N and the estimator chosen before the state; reason: the constant is universal and the protocol must work for every state of the class
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Corollary 19, Eq. (221), p. 64

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Corollary 19 (Interpolation in the vacuum gap).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Corollary 19, Eq. (221), p. 64: "Let ρ(µ, Σ) be an n-mode Gaussian state satisfying Σ ⪰ (1/2 + ν)I for some
ν > 0. For constant failure probability, there is a non-adaptive protocol using only independent heterodyne
measurements that learns ρ(µ, Σ) to trace-distance error ϵ using N = O((n²/ϵ²) min{n, 1 + 1/ν}) copies."

For every failure probability `δ ∈ (0, 1)` there is `C_δ > 0` such that for every `n`, `ν > 0`, `ϵ > 0` there are
`N ≤ C_δ (n²/ϵ²) min{n, 1 + 1/ν}` and a measurable estimator of `N` heterodyne outcomes that learns every Gaussian
state with `Σ ⪰ (½ + ν)I` to trace distance `ϵ` with probability at least `1 − δ`.

**Formalization Note.** "Constant failure probability" is every fixed `δ ∈ (0, 1)`, the constant depending on `δ`;
the proof of Theorem 3 uses `δ = 1/3`. The protocol is chosen before the state. -/
theorem corollary_19 :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : ℝ), 0 < ν → ∀ ϵ : ℝ, 0 < ϵ →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ϵ ^ 2 * min (n : ℝ) (1 + 1 / ν)) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by sorry

end BosonicLearn
