-- Prove2me | Theorems.Thm_BosonicLearn_theorem_8
-- name    : BosonicLearn.theorem_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:34:31.061367+00:00
-- url     : https://prove2.me/theorems/19432860-99c6-4195-902e-8454109fc0d1
-- title:
--   Theorem 8 — heterodyne tomography under a vacuum gap with $O((1+1/\nu)\,n(n+\log(1/\delta))/\epsilon^2)$ copies
-- statement:
--   There is a universal constant $C>0$ such that the following holds. For every $n$, every $\nu>0$ and every $\epsilon,\delta\in(0,1)$ there are
--
--   $$N\le C\Big(1+\frac1\nu\Big)\frac{n(n+\log(1/\delta))}{\epsilon^2}$$
--
--   and a non-adaptive protocol that measures $N$ copies by independent heterodyne detections and always outputs a valid Gaussian state $\hat\rho$, such that for every $n$-mode Gaussian state $\rho(\mu,\Sigma)$ with $\Sigma\succeq(\tfrac12+\nu)I$,
--
--   $$\Pr\Big[\tfrac12\|\hat\rho-\rho(\mu,\Sigma)\|_1\le\epsilon\Big]\ge1-\delta .$$
--
--   For warm states ($\nu\gtrsim1$) this is the classical rate $O(n^2/\epsilon^2)$.
--
--   Differences from the source:
--   - encoding: O(·) and "there is a … protocol" → ∃ C > 0 before every other variable; N and the estimator chosen before the state; reason: the constant is universal and the protocol must work for every state of the class
--   - encoding: a protocol "using only independent heterodyne measurements" → a measurable deterministic estimator of N i.i.d. heterodyne outcomes; reason: the paper's protocol; a deterministic estimator is the stronger existence claim
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 8, Eqs. (205)–(206), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Theorem 8 (Heterodyne tomography under a vacuum gap).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 8, Eqs. (205)–(206), p. 61: "Let ρ(µ, Σ) be an n-mode Gaussian state satisfying Σ ⪰ (1/2 + ν)I
for some ν > 0. For every ϵ, δ ∈ (0, 1), there is a non-adaptive protocol using only independent heterodyne
measurements that always outputs a valid Gaussian state ρ̂ and, with probability at least 1 − δ, satisfies
½‖ρ̂ − ρ(µ, Σ)‖₁ ≤ ϵ using N = O((1 + 1/ν) n(n + log(1/δ))/ϵ²) copies."

There is a universal `C > 0` such that for every `n`, every `ν > 0` and every `ϵ, δ ∈ (0, 1)` there are
`N ≤ C(1 + 1/ν) n(n + log(1/δ))/ϵ²` and a measurable estimator `est` of `N` heterodyne outcomes, every value of
which is a Gaussian state, such that every Gaussian state with `Σ ⪰ (½ + ν)I` is learned to trace distance `ϵ`
with probability at least `1 − δ`.

**Formalization Note.** The protocol (`N` and `est`) is chosen before the state; `O(·)` is one constant uniform in
`n, ν, ϵ, δ`. The estimator is deterministic; that is the paper's protocol. -/
theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : ℝ), 0 < ν → ∀ ϵ δ : ℝ, 0 < ϵ → ϵ < 1 → 0 < δ → δ < 1 →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ϵ ^ 2) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          (∀ y, ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
            IsGaussianState (est y) μ S) ∧
          ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by sorry

end BosonicLearn
