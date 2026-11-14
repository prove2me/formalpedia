-- Prove2me | Theorems.Thm_BosonicLearn_theorem_3
-- name    : BosonicLearn.theorem_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:40:52.54121+00:00
-- url     : https://prove2.me/theorems/40fb0006-f630-4bce-92cd-7d0ef4705eef
-- title:
--   Theorem 3 — tight transition: $\Theta(\frac{n^2}{\varepsilon^2}\min\{n,1+\nu^{-1}\})$ single-copy copies learn Gaussian states with $\Sigma\succeq(\tfrac12+\nu)I$, attained by heterodyne
-- statement:
--   Write $f(n,\varepsilon,\nu)=\dfrac{n^2}{\varepsilon^2}\min\{n,\,1+\nu^{-1}\}$. There are universal constants $\varepsilon_0>0$, $n_0\in\mathbb N$ and $c,C>0$ such that for all $n\ge n_0$, all $0<\varepsilon<\varepsilon_0$ and all $\nu>0$ (which may depend on $n$), for the class of $n$-mode Gaussian states $\rho(\mu,\Sigma)$ with $\Sigma\succeq(\tfrac12+\nu)I$ and arbitrary mean:
--
--   1. **Sufficiency (heterodyne).** Some non-adaptive protocol with $N\le C\,f(n,\varepsilon,\nu)$ independent heterodyne measurements learns every state of the class to trace distance $\varepsilon$ with probability at least $2/3$.
--   2. **Necessity.** Every adaptive single-copy scheme (any POVMs, any outcome space, any randomized estimator) that learns every state of the class to trace distance $\varepsilon$ with probability at least $2/3$ uses $N\ge c\,f(n,\varepsilon,\nu)$ copies.
--
--   Equivalently, $N=\Theta(n^3/\varepsilon^2)$ for $0<\nu<1/n$, $\Theta(n^2/(\nu\varepsilon^2))$ for $1/n\le\nu\le1$, and $\Theta(n^2/\varepsilon^2)$ for $\nu>1$: a quantum-to-classical crossover in learnability between cold states (near the vacuum) and warm states (classical sample complexity).
--
--   Differences from the source:
--   - encoding: N = Θ(f) with universal constants → ∃ c, C > 0 placed with ε₀ and n₀ before n, ε, ν; reason: "universal constants"; ν may depend on n
--   - encoding: "single-copy measurements", possibly adaptive, with an estimator → adaptive schemes of POVMs with an arbitrary measurable outcome space, round laws measurable in the earlier outcomes, and a Markov-kernel estimator to density operators; reason: the paper's model (§1.1 p. 5, §4 p. 19, §5.1 p. 30); measurability makes the transcript a random variable
--   - encoding: "This bound can be achieved by heterodyne measurements" → a measurable deterministic estimator of N i.i.d. heterodyne outcomes, chosen before the state; reason: the paper's protocol (Corollary 19); a deterministic estimator is the stronger existence claim
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 3, Eqs. (6)–(7), pp. 6–7

import Mathlib
import Definitions.Def_BosonicLearn_successProb
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Theorem 3 (Tight transition of learnability).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 3, Eqs. (6)–(7), pp. 6–7: "There exist universal constants ε_0 > 0 and n_0 ∈ ℕ such that the following
holds for all n ≥ n_0 and 0 < ε < ε_0. Under the promise that an n-mode Gaussian state ρ(µ, Σ) satisfies
Σ ≥ (1/2 + ν)I for some ν > 0 that can depend on n, the necessary and sufficient number of copies to learn ρ to ε trace
distance with probability at least 2/3 using single-copy measurements is given by N = Θ((n²/ε²) min{n, 1 + ν^{−1}}).
… This bound can be achieved by heterodyne measurements for all values of ν > 0."

With `f(n, ε, ν) = (n²/ε²)·min{n, 1 + 1/ν}` there are universal `ε₀ > 0`, `n₀`, `c > 0`, `C > 0` such that for all
`n ≥ n₀`, `ε ∈ (0, ε₀)` and `ν > 0`:
1. (sufficiency, heterodyne) some non-adaptive protocol of `N ≤ C·f` independent heterodyne measurements and a
   measurable estimator learns every Gaussian state with `Σ ⪰ (½ + ν)I` to trace distance `ε` with probability `≥ 2/3`;
2. (necessity) every adaptive single-copy scheme on `N` copies, with any measurable outcome space and any randomized
   estimator, that learns every such state to trace distance `ε` with probability `≥ 2/3` has `N ≥ c·f`.

**Formalization Note.** `Θ` is read with universal constants placed, like `ε₀, n₀`, before `n, ε, ν`. The protocol is
chosen before the state. Eq. (7) restates (6) and is not a separate claim. -/
theorem theorem_3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ν : ℝ, 0 < ν →
        (∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν)) ∧
          ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
            Measurable est ∧
            ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (2 / 3) ≤ heterodyneSuccess N est ρ ε) ∧
        (∀ (N : ℕ) (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O)
            (est : Kernel (Fin N → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
          (∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (2 / 3) ≤ successProb S est ρ.coefficients ε) →
          c * ((n : ℝ) ^ 2 / ε ^ 2 * min (n : ℝ) (1 + 1 / ν)) ≤ N) := by sorry

end BosonicLearn
