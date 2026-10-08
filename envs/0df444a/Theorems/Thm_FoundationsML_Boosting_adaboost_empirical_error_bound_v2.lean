-- Prove2me | Theorems.Thm_FoundationsML_Boosting_adaboost_empirical_error_bound_v2
-- name    : FoundationsML.Boosting.adaboost_empirical_error_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:44.524506+00:00
-- url     : https://prove2.me/theorems/fbb0363b-70fb-4401-867e-a8e0672525ac
-- title:
--   Theorem 7.2 — AdaBoost empirical error bound (edge $\gamma\ge0$)
-- statement:
--   **Statement (Theorem 7.2, p. 149, PDF p. 166).** The empirical error of the classifier returned by AdaBoost after $T$ rounds verifies $\hat R_S(f) \le \exp\big(-2\sum_{t=1}^T(\tfrac12-\epsilon_t)^2\big)$. Furthermore, if $\gamma\ge0$ satisfies $\gamma\le\tfrac12-\epsilon_t$ for all $t\in[T]$, then $\hat R_S(f)\le\exp(-2\gamma^2T)$.
--
--   **Formalization Note.** The retired version quantified the second clause over every real $\gamma$, so a negative $\gamma$ satisfied $\gamma\le\tfrac12-\epsilon_t$ trivially while $\exp(-2\gamma^2T)<1$ (disproved with $\epsilon_1=\tfrac12$, $\gamma=-1$). The book's $\gamma$ is the edge by which each base classifier beats random guessing, implicitly non-negative (for $\gamma\ge0$ the clause follows from the first inequality); $0\le\gamma$ is now an explicit hypothesis of the second clause. Everything else is unchanged: `EmpiricalError`/`AdaBoostEpsilon` tie $\epsilon_t$ to AdaBoost's own $D_t$-weighted distribution, the base classifiers are $\{-1,+1\}$-valued on $[T)$ (Figure 7.1), and $\epsilon_t\notin\{0,1\}$ excludes the rounds where the book's $\alpha_t=\pm\infty$ is not representable.
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
addition `γ ≥ 0` satisfies `γ ≤ 1/2 − ε_t` for all `t ∈ [T]`, then `R̂_S(f) ≤ exp(−2γ²T)`.

**Formalization Note.** Replaces `adaboost_empirical_error_bound`, whose second clause
quantified over every real `γ`, so a negative `γ` satisfied `γ ≤ 1/2 − ε_t` trivially while
`exp(−2γ²T) < 1` (disproved with `ε_1 = 1/2`, `γ = −1`). The book's `γ` is the edge by which
each base classifier beats random guessing, implicitly non-negative (the clause is only
meaningful for `γ ≥ 0`, where it follows from the first inequality); `0 ≤ γ` is now explicit.
Everything else is unchanged: `EmpiricalError` and `AdaBoostEpsilon` tie `ε_t` to AdaBoost's
own `D_t`-weighted sample distribution; the `{−1,+1}`-valued range of each `h t` on `[T)` is
the standing hypothesis of Figure 7.1; `hne` excludes `ε_t ∈ {0,1}`, where the book's
`α_t = ±∞` is not representable (Lean's `Real.log` would silently give `α_t = 0`). -/
theorem adaboost_empirical_error_bound_v2 {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1) :
    EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) ∧
      (∀ γ : ℝ, 0 ≤ γ → (∀ t < T, γ ≤ 1 / 2 - AdaBoostEpsilon S y h t) →
        EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
          Real.exp (-2 * γ ^ 2 * T)) := by sorry

end FoundationsML.Boosting
