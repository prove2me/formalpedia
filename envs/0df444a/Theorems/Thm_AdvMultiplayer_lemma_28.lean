-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_28
-- name    : AdvMultiplayer.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:16:17.059757+00:00
-- url     : https://prove2.me/theorems/eea7c7e6-a0c9-4221-a931-19c7f1549ab5
-- title:
--   Lemma 28 — uniform exclusion of false bootstrap rows
-- statement:
--   On the construction branch there is a public event of probability at least $1-N^{-1}$ on which the following holds simultaneously for every reward support and every true index $J$: conditional on the complete numerical public output and on that index, the private probability of any forward failure is at most $B_{\mathrm{boot}}^{-1}$.
--
--   Differences from the source:
--   - encoding: every reward support → every rounded matrix, quantified after the table; reason: each support is that of a rounded matrix, and the execution before launch depends only on the support
--   - reading: no hypothesis in the statement → construction branch (45); reason: the constants of the lemma are defined only there
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 28, p.61

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 28 (uniform exclusion of false bootstrap rows).** Gan, arXiv:2610.05688, Lemma 28, p.61.
There is a public event of probability at least `1 - N⁻¹` on which, simultaneously for every reward
support and every true index `J`, the private probability of any forward failure is at most `B_boot⁻¹`,
conditional on the complete numerical public output and on that index.

**Formalization Note.** The event is a set of tables. Each reward support is that of a rounded matrix,
and the execution before launch depends on the rewards only through their support, so `∀ r` is "every
reward support"; it is quantified after the table. Fixing the table and `J = j` leaves the tapes, whose
law is `tapeLaw`. `A` and `q_dec` are the constants of `Size`. -/
theorem lemma_28 (p : Size) (hb : p.branch) :
    ∃ G : Set (Table p), MeasurableSet G ∧ ENNReal.ofReal (1 - 1 / (p.N : ℝ)) ≤ tableLaw p G ∧
      ∀ d : TableData p, Sum.inr d ∈ G → ∀ r : Rewards p, IsRounded p r →
        ∀ j ∈ Finset.Icc 1 p.M,
          tapeLaw p {ω | forwardFailure p d (roundAt p d ⟨some j, true⟩ r ω) j}
            ≤ ENNReal.ofReal (1 / (p.Bboot : ℝ)) := by sorry

end AdvMultiplayer
