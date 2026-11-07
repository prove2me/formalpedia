-- Prove2me | Theorems.Thm_BeyondDS_lemma_7_1
-- name    : BeyondDS.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:50.831322+00:00
-- url     : https://prove2.me/theorems/48fbcce0-a3d4-4f77-8055-907dab808c54
-- title:
--   Lemma 7.1 — trials to a fixed target miss it with probability at most $(1-1/n)^L\le e^{-L/n}$
-- statement:
--   Fix a target $u\in[n]$ and an adaptive process of bounded length in which some steps are completed random transmission trials with fresh destinations uniform on $[n]$, each trial being selected (counted) or not by a decision made before its destination is drawn. For every positive integer $L$,
--
--   $$\Pr\big[\text{at least $L$ selected trials occur and none of the first $L$ selected destinations is $u$}\big]\le\Big(1-\frac1n\Big)^L\le e^{-L/n}.$$
--
--   This is the single calculation that covers adaptive choices of senders and interruptions in every probabilistic estimate of §§7–8.
--
--   **Formalization Note** The process has free kernels, so any adaptive adversary and corruption rule embeds.
--
--   Differences from the source:
--
--   - encoding: "a finite phase of an execution" → a process of at most `fuel` steps whose steps are stop, noise or a trial with a predictably fixed selection bit; reason: every finite phase of an execution of the model is such a process, with the execution in the state
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 7.1, p.23 (PDF p.24), eq. (10)

import Mathlib
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS

/-- Lemma 7.1 (Trials to a fixed target), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.23 (PDF 24), eq. (10): for a predictably selected
sequence of completed random trials in a finite phase, the probability that at least `L` selected trials occur and none
of their first `L` destinations equals `u` is at most `(1 − 1/n)^L ≤ exp(−L/n)`.

**Formalization Note.** The process is `TrialStep` with free kernels, so any adaptive adversary and any corruption rule embeds;
`sel` is fixed before the destination is drawn, which is the definition of "selected predictably". -/
theorem lemma_7_1 {n : ℕ} [NeZero n] {σ : Type} (kind : σ → TrialStep n σ) (u : Fin n) (fuel : ℕ) (s₀ : σ)
    (L : ℕ) (hL : 0 < L) :
    (selectedDests kind fuel s₀).toOuterMeasure {l | L ≤ l.length ∧ u ∉ l.take L} ≤
        ENNReal.ofReal ((1 - 1 / (n : ℝ)) ^ L) ∧
      (1 - 1 / (n : ℝ)) ^ L ≤ Real.exp (-((L : ℝ) / n)) := by sorry

end BeyondDS
