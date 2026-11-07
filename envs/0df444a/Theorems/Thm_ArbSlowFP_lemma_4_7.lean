-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_4_7
-- name    : ArbSlowFP.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:59.530949+00:00
-- url     : https://prove2.me/theorems/7903d047-1a0e-4b11-a696-c977f9445a9a
-- title:
--   Lemma 4.7 — one setup action realizes a score process from zero counts
-- statement:
--   Let $A\in\mathbb Q^{m\times m}$ be skew-symmetric, and let $(w_t)$ be the action sequence of a score process with unique maximizers and initial vector $g=f+\beta$. In the game $\hat A$ of $(22)$ with one additional action, simultaneous fictitious play from zero counts with both players choosing the setup action in the first round exists. For every such run and every $t\ge0$, both players play $w_t$ at time $t+1$, this is the unique best response of each player at that time, and the row scores on the recurrent actions at time $t+1$ equal the process scores at time $t$ plus the common constant $1-\min_ig_i$. In particular the setup action is never played again.
--
--   This realizes the auxiliary process as genuine fictitious play.
--
--   **Formalization Note** Run and best-response sets are computed in the real cast of $\hat A$, with the setup action `none`.
--
--   Differences from the source:
--   - encoding: run of (3) with both players choosing the setup action in round 0 → every sequence of plays satisfying (3) with those first plays, together with a clause that one exists; reason: the plays are the data and ties at t = 0 are free; the statement does not assume uniqueness of the run
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.30, Lemma 4.7

import Mathlib
import Definitions.Def_ArbSlowFP_IsFPRun
import Definitions.Def_ArbSlowFP_ValidFrom
import Definitions.Def_ArbSlowFP_setupGame

open Matrix

namespace ArbSlowFP

/-- Lemma 4.7, p.30 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): a rational
skew-symmetric score process with unique maximizers from `g = f + β` is realized, up to a common score
translation, by simultaneous fictitious play from zero counts in the game (22) with one additional
action. If both players choose the setup action in the first round, it is never played again.

**Formalization Note.** Every run with `i 0 = j 0 = none` satisfies `i (t+1) = j (t+1) = some (w t)`,
with unique best responses for `t ≥ 1`, and row scores at `t + 1` on the recurrent actions equal the
process scores plus the constant `1 - min g`. A run exists. -/
theorem lemma_4_7 {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℚ) (hA : Aᵀ = -A)
    (g : ι → ℚ) (w : ℕ → ι) (hw : ∀ t, IsUniqueMax (procScore A g w t) (w t)) :
    (∃ i j, IsFPRun (toReal (setupGame A g)) i j ∧ i 0 = none ∧ j 0 = none) ∧
    ∀ i j, IsFPRun (toReal (setupGame A g)) i j → i 0 = none → j 0 = none →
      ∀ t,
        i (t + 1) = some (w t) ∧ j (t + 1) = some (w t) ∧
        rowBR (toReal (setupGame A g)) (countVec j (t + 1)) = {some (w t)} ∧
        colBR (toReal (setupGame A g)) (countVec i (t + 1)) = {some (w t)} ∧
        ∀ x, (toReal (setupGame A g) *ᵥ countVec j (t + 1)) (some x) =
          ((procScore A g w t x + (1 - minEntry g) : ℚ) : ℝ) := by sorry

end ArbSlowFP
