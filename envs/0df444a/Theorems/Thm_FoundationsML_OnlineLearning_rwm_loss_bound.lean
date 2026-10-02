-- Prove2me | Theorems.Thm_FoundationsML_OnlineLearning_rwm_loss_bound
-- name    : FoundationsML.OnlineLearning.rwm_loss_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:22:32.629752+00:00
-- url     : https://prove2.me/theorems/1b5d3ce6-002c-4353-be40-3a14133fa23e
-- title:
--   Theorem 8.4 — Randomized Weighted Majority loss bound
-- statement:
--   **Statement (Theorem 8.4, p. 184, PDF p. 201).** Fix $\beta\in[1/2,1)$. Then, for any
--   $T\ge1$, the loss of algorithm RWM on any sequence satisfies $L_T \le
--   \frac{\log N}{1-\beta} + (2-\beta)L_T^{\min}$. In particular, for
--   $\beta=\max\{1/2,1-\sqrt{(\log N)/T}\}$, $L_T \le L_T^{\min} + 2\sqrt{T\log N}$. A
--   self-contained showcase of the chapter's potential-function proof technique (also used for
--   Theorem 8.3's WM mistake bound and Theorem 8.6's regret bound), on the RWM algorithm's own
--   weighted-mixture *loss* (not a `0`-`1` mistake count).
--
--   **Formalization Note.** `RWMCumulativeLoss`/`RWMMinExpertLoss` are RWM's own loss (not a
--   mistake count), per `BRIEF.md`'s pitfall note distinguishing this chapter's loss- and
--   mistake-bound theorems. Checked against the platform's
--   `OnlineConvexOpt.Introduction.randomized_weighted_majority_mistake_bound` (Hazan series):
--   that lemma bounds a *mistake* count with a `(1+ε)` multiplier and additive `log(N)/ε`, a
--   different form from this *loss* bound's `1/(1-β)` term and distinct optimal-`β`
--   substitution — not reused, disclosed in `description.md`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 184, Theorem 8.4 (PDF p. 201)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_RWMCumulativeLoss
import Definitions.Def_FoundationsML_OnlineLearning_RWMMinExpertLoss

namespace FoundationsML.OnlineLearning

/-- Theorem 8.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 184, PDF p. 201). Fix `β ∈ [1/2,1)`. Then, for any `T ≥ 1`, the loss of
algorithm RWM on any sequence satisfies `L_T ≤ log(N)/(1−β) + (2−β)L_T^min`. In particular,
for `β = max{1/2, 1 − sqrt(log(N)/T)}`, `L_T ≤ L_T^min + 2 sqrt(T log N)`. -/
theorem rwm_loss_bound {N : ℕ} (hN : 0 < N) (l : ℕ → Fin N → ℝ) (hl : ∀ t i, l t i = 0 ∨ l t i = 1)
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ β : ℝ, 1 / 2 ≤ β → β < 1 →
      RWMCumulativeLoss β N l T ≤
        Real.log N / (1 - β) + (2 - β) * RWMMinExpertLoss N l T) ∧
    RWMCumulativeLoss (max (1 / 2) (1 - Real.sqrt (Real.log N / T))) N l T ≤
      RWMMinExpertLoss N l T + 2 * Real.sqrt (T * Real.log N) := by sorry

end FoundationsML.OnlineLearning
