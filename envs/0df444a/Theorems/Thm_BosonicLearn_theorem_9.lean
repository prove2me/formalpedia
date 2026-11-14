-- Prove2me | Theorems.Thm_BosonicLearn_theorem_9
-- name    : BosonicLearn.theorem_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:41:10.045256+00:00
-- url     : https://prove2.me/theorems/16731bbd-399e-4e99-8c4c-fdf13648c832
-- title:
--   Theorem 9 — any (collective) scheme learning passive states with $\Sigma\succeq(\tfrac12+\nu)I$ needs $N\ge Cn^2/\varepsilon^2$
-- statement:
--   There are constants $C,\varepsilon_0>0$ and $n_0$ such that for every $\nu>0$, every $\varepsilon\in(0,\varepsilon_0)$ and every $n\ge n_0$: any scheme, including arbitrary collective (entangled) measurements on $\rho^{\otimes N}$, that learns every $n$-mode passive Gaussian state $\rho(0,\Sigma)$ with $\Sigma\succeq(\tfrac12+\nu)I$ to trace distance $\varepsilon$ with probability $2/3$ needs
--
--   $$N\ge C\,\frac{n^2}{\varepsilon^2}.$$
--
--   It is the warm-state half of the lower bound in Theorem 3: $n^2/\varepsilon^2$ copies are necessary even for entangled measurements.
--
--   Differences from the source:
--   - reading: "for any ν > 0, 0 < ε < ε₀, and sufficiently large n" → n₀ chosen before ν and ε; reason: the stronger reading; the proof's "sufficiently large n" (ensemble (223), Fano (229)) does not depend on ν or ε, and Theorem 3 needs it uniform
--   - encoding: "any scheme", "arbitrary collective measurements" → a POVM on the N-copy Fock space whose outcome is the estimated density operator; reason: measurement followed by any classical post-processing is again such a POVM
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 9, p. 65 (collective measurements, p. 67)

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_promiseClass
import Definitions.Def_BosonicLearn_IsPassive
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Theorem 9 (Matching lower bound for warm states, any collective scheme).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 9, p. 65: "There exist constants C > 0 and ε_0 > 0 such that the following holds: For any ν > 0,
0 < ε < ε_0, and sufficiently large n, any scheme that can learn any passive Gaussian state ρ(0, Σ) to ε trace
distance with 2/3 probability with the promise that Σ ≥ (1/2 + ν)I requires at least N ≥ Cn²/ε² copies."
The proof covers "arbitrary collective measurements" (p. 67).

There are `C, ε₀ > 0` and `n₀` such that for every `ν > 0`, `ε ∈ (0, ε₀)`, `n ≥ n₀`, and every POVM on `N` copies
(entangled across copies) whose outcome is the estimate: if every passive Gaussian state with `Σ ⪰ (½ + ν)I` is
learned to trace distance `ε` with probability at least `2/3`, then `N ≥ Cn²/ε²`.

**Formalization Note.** "Sufficiently large n" is read uniformly in `ν` and `ε` (`n₀` before `ν, ε`); see the
Differences list. -/
theorem theorem_9 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∀ ν : ℝ, 0 < ν → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ n : ℕ, n₀ ≤ n →
      ∀ (N : ℕ) (E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n)))),
        (∀ ρ ∈ promiseClass n ν, IsPassive ρ → ENNReal.ofReal (2 / 3) ≤ collectiveSuccess E ρ ε) →
        C * ((n : ℝ) ^ 2 / ε ^ 2) ≤ N := by sorry

end BosonicLearn
