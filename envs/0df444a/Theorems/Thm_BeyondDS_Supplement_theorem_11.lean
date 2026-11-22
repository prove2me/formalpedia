-- Prove2me | Theorems.Thm_BeyondDS_Supplement_theorem_11
-- name    : BeyondDS.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:13:26.621845+00:00
-- url     : https://prove2.me/theorems/defbcce0-0798-4a22-aff1-87a0d6fc9d28
-- title:
--   Theorem 11 — high-probability sender bound: CSU and $M\le C$ jointly with probability $1-\eta$ force $\eta\ge\frac{1-2c}{5-2c}$, $c=C/(f+1)$
-- statement:
--   Let $n=2f+1$ with $f\ge1$, in the model of §12: binary inputs, point-to-point messages, and an arbitrary input-independent correlated setup whose distribution is unchanged by passive corruptions, under any fixed delivery schedule. Let $M$ be the number of distinct honest senders.
--
--   Suppose that, for every corrupt set of at most $f$ passively corrupt players and every input assignment, the protocol satisfies consensus with strong unanimity and $M\le C$ jointly with probability at least $1-\eta$. Here $\eta\in[0,1]$ and $C$ is a real bound with $0\le C\le(f+1)/2$; write $c=C/(f+1)$. Then
--   $$\eta\;\ge\;\frac{1-2c}{5-2c}.$$
--
--   For $C=0$ this gives $\eta\ge1/5$, and the bound is positive for every $C<(f+1)/2$: a protocol in which few distinct players ever send cannot have small error.
--
--   **Formalization Note** The protocol class is `LocalProtocol`. Senders are counted over the whole execution, after decisions and on failure histories. `MeasurableRun` is the standing measurability convention.
--
--   Differences from the source:
--   - generalization: the joint guarantee holds for every permitted adversary and input assignment → it is assumed only for static passive corruptions of at most f players; reason: every class of permitted adversaries contains them, so the hypothesis is weaker
--   - generalization: private tapes independent of inputs and setup; one fixed permitted delivery schedule → the tapes are part of one input-independent sample with no independence required; the statement holds for every fixed delivery schedule; reason: the proof couples executions on one probability space and uses no independence
--   - encoding: executions in the source's communication model; probability of the joint event → discrete steps with a delay function; a measurability convention on the run; reason: Lean conventions; same instances
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 11, p.58 (PDF p.59), eq. (70); §12, p.57 (PDF p.58), model and error event

import Mathlib
import Definitions.Def_BeyondDS_Supplement_LocalProtocol

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BeyondDS.Supplement

/-- Theorem 11 (High-probability sender bound), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.58 (PDF 59), in the model of §12, p.57 (PDF 58; n = 2f + 1 players, f ≥ 1): "Suppose that, for every permitted adversary and input assignment, the protocol satisfies CSU and M ≤ C jointly with probability at least 1 − η. Here η ∈ [0, 1] and C is a real bound with 0 ≤ C ≤ (f + 1)/2; write c = C/(f + 1). Then η ≥ (1 − 2c)/(5 − 2c). (70)"

Let `n = 2f + 1` with `f ≥ 1`, let `P` be a protocol of the local model (`LocalProtocol`) run under a fixed delivery schedule `delay`, and let `η ∈ [0, 1]` and `0 ≤ C ≤ (f + 1)/2`. If for every static passive corruption `F` of at most `f` players and every input assignment `x`, the event "CSU holds and the number `M` of distinct honest senders is at most `C`" has probability at least `1 − η`, then `η ≥ (1 − 2c)/(5 − 2c)` with `c = C/(f + 1)`.

**Formalization Note.** The hypothesis is required only of the static passive adversaries, which every class of permitted adversaries contains; this is weaker than the source's hypothesis. `M` counts senders over the whole unbounded execution. `MeasurableRun` is the standing measurability convention. -/
theorem theorem_11 (f : ℕ) (hf : 1 ≤ f) (P : LocalProtocol (2 * f + 1) Bool)
    (delay : ℕ → Fin (2 * f + 1) → Fin (2 * f + 1) → ℕ) (hP : P.MeasurableRun delay)
    (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ ((f : ℝ) + 1) / 2)
    (h : ∀ (F : Finset (Fin (2 * f + 1))), F.card ≤ f → ∀ x : Fin (2 * f + 1) → Bool,
      ENNReal.ofReal (1 - η) ≤
        P.μ {ω | P.CSU delay F x ω ∧ (P.numSenders delay F x ω : ℝ) ≤ C}) :
    (1 - 2 * (C / ((f : ℝ) + 1))) / (5 - 2 * (C / ((f : ℝ) + 1))) ≤ η := by sorry

end BeyondDS.Supplement
