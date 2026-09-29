-- Prove2me | Theorems.Thm_FoundationsML_Boosting_adaboost_empirical_error_bound
-- name    : FoundationsML.Boosting.adaboost_empirical_error_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:30.559328+00:00
-- url     : https://prove2.me/theorems/8d1d87b0-588d-43a6-9fcb-503fe3cf16fa
-- title:
--   Theorem 7.2 — AdaBoost empirical error bound (milestone)
-- statement:
--   **Statement (Theorem 7.2, p. 149, PDF p. 166).** The empirical error of the classifier
--   returned by AdaBoost verifies $\hat R_S(f) \le \exp(-2\sum_{t=1}^T(1/2-\varepsilon_t)^2)$.
--   Furthermore, if $\gamma\le(1/2-\varepsilon_t)$ for all $t\in[T]$, then
--   $\hat R_S(f)\le\exp(-2\gamma^2T)$.
--
--   This is the chapter's first main result: it shows AdaBoost's training error decreases
--   exponentially fast in the number of rounds, whenever each round's base classifier beats
--   random guessing by a margin (the "edge" $\gamma$).
--
--   **Formalization Note.** `AdaBoostEpsilon`/`AdaBoostEnsemble` already tie $\varepsilon_t$ and
--   $f$ to AdaBoost's own recursion (per `BRIEF.md`'s trivialization warning), so no separate
--   hypothesis links them. **Revision (2026-09-19).** Added `hne`, excluding $\varepsilon_t\in
--   \{0,1\}$ for every round: `AdaBoostAlpha` is a total Lean function whose
--   `Real.log`-of-a-zero-division convention would otherwise let a perfect or perfectly-wrong
--   round silently zero out $\alpha_t$ instead of the book's intended $\pm\infty$, which is what
--   should make such a round dominate the ensemble — without `hne` the theorem is false as
--   stated (concrete counterexample: $m=1$, $T=1$, $h_0(x)=1$, $y_0=1$, forcing
--   $\varepsilon_0=0$, `AdaBoostAlpha`'s junk value $\alpha_0=0$, and empirical error $1$ against
--   a claimed bound of $\exp(-1/2)\approx0.61$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 149, Theorem 7.2 (PDF p. 166)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalError
import Definitions.Def_FoundationsML_Boosting_AdaBoostEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- Theorem 7.2 (AdaBoost empirical error bound; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 149, PDF p. 166). Let `f` be the function
returned by AdaBoost after `T` rounds of boosting on a sample `(S, y)` with base classifiers
`h : ℕ → X → ℝ` valued in `{−1,+1}`. Then `R̂_S(f) ≤ exp(−2 ∑_{t=1}^T (1/2 − ε_t)²)`, and if in
addition `γ ≤ 1/2 − ε_t` for all `t ∈ [T]`, then `R̂_S(f) ≤ exp(−2γ²T)`.

**Formalization Note.** `EmpiricalError` and `AdaBoostEpsilon` already tie `ε_t` to AdaBoost's
own `D_t`-weighted sample distribution (per `BRIEF.md`'s trivialization warning), so no
separate hypothesis is needed to connect them. The `{−1,+1}`-valued range of each `h t` on
`[T)` is the standing hypothesis of Figure 7.1 (§7.2, before the range is generalized to
`[−1,1]` later in the section). `hne` excludes `ε_t ∈ {0,1}` for every round: `AdaBoostAlpha` is
a total Lean function whose `Real.log`-of-a-zero-division convention would otherwise let a
perfect or perfectly-wrong round silently zero out `α_t` instead of the book's intended `±∞`,
which is what should make such a round dominate the ensemble. -/
theorem adaboost_empirical_error_bound {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1) :
    EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) ∧
      (∀ γ : ℝ, (∀ t < T, γ ≤ 1 / 2 - AdaBoostEpsilon S y h t) →
        EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
          Real.exp (-2 * γ ^ 2 * T)) := by sorry

end FoundationsML.Boosting
