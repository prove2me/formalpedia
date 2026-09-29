-- Prove2me | Theorems.Thm_FoundationsML_Boosting_adaboost_margin_bound
-- name    : FoundationsML.Boosting.adaboost_margin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:31.295316+00:00
-- url     : https://prove2.me/theorems/a67ae01a-a6f4-4160-8e93-d4fa06fbe231
-- title:
--   Theorem 7.7 — AdaBoost margin bound (goal)
-- statement:
--   **Statement (Theorem 7.7, p. 159, PDF p. 176).** Let $f=\sum_{t=1}^T\alpha_th_t$ denote the
--   function returned by AdaBoost after $T$ rounds of boosting and assume for all $t\in[T]$
--   that $\varepsilon_t<1/2$, which implies $\alpha_t>0$. Then, for any $\rho>0$,
--   $$\hat R_{S,\rho}(\bar f) \le 2^T\prod_{t=1}^T\sqrt{\varepsilon_t^{1-\rho}(1-\varepsilon_t)^{1+\rho}}.$$
--
--   This is the chapter's capstone: a bound on the *empirical margin loss* of AdaBoost's own
--   normalized output, decreasing (under the weak-learning condition) as $T$ grows, which
--   (combined with Corollary 7.5) explains why AdaBoost's test error can keep improving even
--   after its training error reaches zero — the empirical phenomenon that opens §7.3.1.
--
--   **Formalization Note.** `ε_t^{1-ρ}`/`(1-ε_t)^{1+ρ}` use `Real.rpow` (real-exponent power,
--   since $\rho\in\mathbb R$). `α_t>0` is not stated as a separate hypothesis (it is a
--   consequence of `hweak` via `AdaBoostAlpha`, per `BRIEF.md`'s pitfall note, not re-derived
--   since only the statement is drafted). `f̄` is `AdaBoostNormalizedEnsemble`, matching the
--   book's use of the normalized combination (not the raw `f`) in this statement.
--
--   **Revision (2026-09-19).** Strengthened `hweak` from $\varepsilon_t<1/2$ to
--   $0<\varepsilon_t<1/2$ for every round, excluding the same degenerate $\varepsilon_t=0$ case
--   as Theorem 7.2's `hne` above (the book's own sentence, "assume ... that $\varepsilon_t<1/2$,
--   which implies $\alpha_t>0$," already presupposes $\varepsilon_t$ is a well-defined real
--   number for the comparison $\alpha_t>0$ to make sense — which requires $\varepsilon_t\ne0$ —
--   so $0<\varepsilon_t<1/2$ is a more literal reading of the book's own sentence, not merely a
--   defensive addition). Without it the theorem is false as stated (same counterexample family
--   as Theorem 7.2's `hne`, instantiated at $\rho=1/2$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 159, Theorem 7.7 (PDF p. 176)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizedEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- Theorem 7.7 (AdaBoost margin bound; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 159, PDF p. 176 — this mission's goal). Let
`f = ∑_{t=1}^T α_t h_t` be the function returned by AdaBoost after `T` rounds of boosting, and
assume for all `t ∈ [T]` that `ε_t < 1/2` (which implies `α_t > 0`). Then, for any `ρ > 0`,
`R̂_{S,ρ}(f̄) ≤ 2^T ∏_{t=1}^T sqrt(ε_t^{1−ρ} (1−ε_t)^{1+ρ})`, where `f̄ = f / ∑_t α_t`.

**Formalization Note.** `ε_t^{1-ρ}` and `(1-ε_t)^{1+ρ}` use `Real.rpow` (the `ℝ`-exponent
power, notation `^`, since `ρ : ℝ`), matching the book's real-exponent expression exactly.
`hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1/2` is the
weak-learning hypothesis; per `BRIEF.md`'s pitfall note, `α_t > 0` is *not* stated as a separate
free hypothesis, since it is a consequence of `hweak` via `AdaBoostAlpha`'s definition (not
re-derived here, since only the theorem's statement is drafted). The `0 < ε_t` half of `hweak`
excludes the degenerate case `ε_t = 0`, where `AdaBoostAlpha`'s `Real.log`-of-a-zero-division
convention would silently zero out `α_t` instead of the book's intended `+∞`; the book's own
sentence, "assume for all `t∈[T]` that `ε_t < 1/2`, which implies `α_t > 0`," already
presupposes `ε_t` is a well-defined real number for the comparison `α_t > 0` to make sense —
which requires `ε_t ≠ 0` in the first place — so `0 < ε_t < 1/2` is arguably a more literal
reading of the book's own sentence, not merely a defensive addition. `AdaBoostNormalizedEnsemble`
is `f̄` (the normalized combination), matching the book's use of `f̄`, not the raw `f`, in this
statement. -/
theorem adaboost_margin_bound {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1 / 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    EmpiricalMarginLoss ρ S y (AdaBoostNormalizedEnsemble S y h T) ≤
      2 ^ T * ∏ t ∈ Finset.range T,
        Real.sqrt ((AdaBoostEpsilon S y h t) ^ (1 - ρ) *
          (1 - AdaBoostEpsilon S y h t) ^ (1 + ρ)) := by sorry

end FoundationsML.Boosting
