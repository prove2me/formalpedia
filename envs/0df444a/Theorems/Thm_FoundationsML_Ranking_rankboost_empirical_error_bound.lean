-- Prove2me | Theorems.Thm_FoundationsML_Ranking_rankboost_empirical_error_bound
-- name    : FoundationsML.Ranking.rankboost_empirical_error_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:04:12.101983+00:00
-- url     : https://prove2.me/theorems/707d7279-3521-4c59-abd4-7da0c5890d21
-- title:
--   Theorem 10.3 — RankBoost empirical error bound
-- statement:
--   **Statement (Theorem 10.3, p. 247, PDF p. 264).** The empirical error of the function `f`
--   returned by RankBoost after `T` rounds verifies $\hat R_S(f) \le \exp(-2\sum_{t=1}^T
--   ((\epsilon_t^+-\epsilon_t^-)/2)^2)$, and if $0<\gamma\le(\epsilon_t^+-\epsilon_t^-)/2$ for
--   all $t\in[T]$, then $\hat R_S(f) \le \exp(-2\gamma^2 T)$, provided every round has a base
--   ranker that is neither perfectly correct nor perfectly wrong on the sample's pairs (i.e.
--   $\epsilon_t^+>0$ and $\epsilon_t^->0$ for all $t<T$). The ranking analogue of chunk
--   `07-boosting`'s Theorem 7.2 (AdaBoost), with RankBoost's own pairwise `ε^+`/`ε^-` in place
--   of AdaBoost's single `ε_t`.
--
--   **Formalization Note.** `RankBoostEpsilonPlus`/`RankBoostEpsilonMinus` already tie
--   `ε_t^+`/`ε_t^-` to RankBoost's own `D_t`-weighted pairwise-outcome fractions, so no
--   separate hypothesis is needed to connect them (mirrors chunk `07`'s own note on this point).
--   The `{0,1}`-valued range of each base ranker `h t` on `[T)` matches Figure 10.1's own
--   `H ⊆ {0,1}^X`. The non-degeneracy hypothesis `hne` (`0 < ε_t^+` and `0 < ε_t^-` for every
--   round `t < T`) is required because `RankBoostAlpha`'s Lean formalization is a total
--   function: at `ε_t^+ = 0` or `ε_t^- = 0` its `Real.log`-of-a-zero-division convention
--   silently returns `0` for `α_t` instead of the `±∞` the book's algorithm intends for a
--   round whose base ranker is perfectly correct or perfectly wrong, which — left unguarded —
--   makes the bound false rather than merely unprovable (a concrete counterexample is recorded
--   in `SELF_REVIEW.md`). The book's own printed standing assumption `ϵ_t^+ − ϵ_t^- > 0` (p.
--   246) does not exclude this degenerate case, since `ε_t^+=1, ε_t^-=0` satisfies it.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 247, Theorem 10.3 (PDF p. 264)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_EmpiricalError
import Definitions.Def_FoundationsML_Ranking_RankBoostEnsemble
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonPlus
import Definitions.Def_FoundationsML_Ranking_RankBoostEpsilonMinus

namespace FoundationsML.Ranking

/-- Theorem 10.3 (RankBoost empirical error bound; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 247, PDF p. 264). Let `f` be
the function returned by RankBoost after `T` rounds of boosting on a pairwise-labeled sample
`(S1, S2, y)` with base rankers `h : ℕ → X → ℝ` valued in `{0,1}`. Then
`R̂_S(f) ≤ exp(−2 ∑_{t=1}^T ((ε_t^+ − ε_t^-)/2)²)`, and if in addition
`0 < γ ≤ (ε_t^+ − ε_t^-)/2` for all `t ∈ [T]`, then `R̂_S(f) ≤ exp(−2γ²T)`.

**Formalization Note.** `hne` excludes `ε_t^+ = 0` or `ε_t^- = 0` for every round: `RankBoostAlpha`
is a total Lean function whose `Real.log`-of-a-zero-division convention would otherwise let a
round with a perfectly correct or perfectly wrong base ranker silently zero out `α_t` instead of
the book's intended `±∞`, which is what should make such a round dominate the ensemble. The
book's own printed standing assumption "`ϵ+_t − ϵ−_t > 0`" (p. 246, PDF p. 263) is not strong
enough to exclude this: `ε_t^+ = 1, ε_t^- = 0` satisfies `ε_t^+ − ε_t^- > 0` and is exactly the
degenerate case `hne` rules out, so `hne` is a strictly stronger, explicit reading of the book's
intent, not a restatement of its printed assumption. -/
theorem rankboost_empirical_error_bound {X : Type*} {m : ℕ} (hm : 0 < m)
    (S1 S2 : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 0 ∨ h t x = 1)
    (hne : ∀ t < T, 0 < RankBoostEpsilonPlus S1 S2 y h t ∧
      0 < RankBoostEpsilonMinus S1 S2 y h t) :
    EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T,
          ((RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) ^ 2) ∧
      (∀ γ : ℝ, (∀ t < T, 0 < γ ∧
            γ ≤ (RankBoostEpsilonPlus S1 S2 y h t - RankBoostEpsilonMinus S1 S2 y h t) / 2) →
        EmpiricalError S1 S2 y (RankBoostEnsemble S1 S2 y h T) ≤
          Real.exp (-2 * γ ^ 2 * T)) := by sorry

end FoundationsML.Ranking
