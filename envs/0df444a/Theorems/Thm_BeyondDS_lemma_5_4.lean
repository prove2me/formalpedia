-- Prove2me | Theorems.Thm_BeyondDS_lemma_5_4
-- name    : BeyondDS.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:13:45.614199+00:00
-- url     : https://prove2.me/theorems/37e99ea6-3cec-4df1-a969-cbcb52d561d8
-- title:
--   Lemma 5.4 — prepared-candidate progress, with probability at least $(t+1)/n-\zeta$
-- statement:
--   1. Consider an outcome of the compiler with no forgery and every required delivery, and an iteration $1\le r\le J$ in which every forever-honest player completed the Commit call. If the elected $L_r$ was uncorrupted through the last round of the Proposal call, then every forever-honest player holds a verifying termination certificate at the end of iteration $r$.
--   2. For every election law at statistical distance at most $\zeta$ from uniform and every configuration with at most $t$ corrupted players, the election output is uncorrupted with probability at least $(t+1)/n-\zeta$, conditional on the transcript.
--
--   "This probability assertion does not condition on future authentication success."
--
--   Differences from the source:
--
--   - reading: "no honest player has halted" → every forever-honest player has an output of the Commit call of iteration r; reason: a player that halted earlier has no such output
--   - reading: "obtains a termination certificate by the end of iteration r" → the output of the Commit call of iteration r holds a verifying termination certificate; reason: the end of iteration r is that call's deadline
--   - reading: "conditional on the transcript at that deadline" → for every configuration at the deadline, under the election law given its transcript; reason: the election is drawn at that boundary from the law given the transcript
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model
--   - generalization: the late common election oracle of §§4.3, 5.1, in the first clause → any election law, a function of the transcript at the reveal boundary; reason: the progress conclusion assumes the elected candidate honest through Proposal and holds whatever law elected it; the oracle is one such law (the probability clause keeps ElectNear)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 5.4, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Lemma 5.4 (Prepared-candidate progress), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.18 (PDF 19): suppose authentication holds throughout the capped execution, no honest player has halted, the required dissemination invocations succeed, and candidate
`L_r` remains honest through the Proposal deadline. Then every forever-honest player obtains a termination certificate by the end of iteration `r`. Conditional on the transcript at that deadline, the event that `L_r` was honest through the deadline has probability at least `(t + 1)/n − ζ`. "This probability assertion does
not condition on future authentication success."

**Formalization Note.** Call `6r` is the Commit call of iteration `r` and call `6r − 2` its Proposal call; "no honest player has halted" through iteration `r` is the existence of each forever-honest player's output of call `6r`. The probability clause holds for every configuration at the deadline, with `E` at distance `ζ`
from uniform (`ElectNear`) conditional on every transcript. -/
theorem lemma_5_4 :
    (∀ (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (A : Adversary P.n CMsg CSt)
    (ω : Config P.n CMsg CSt A.σ) (hω : ω ∈ (exec (compiler J) S P x E A).support)
    (hF : ¬ Forge ω) (hD : Delivered P (J P) ω) (r : ℕ) (hr₁ : 1 ≤ r) (hrJ : r ≤ J P)
      (hNoHalt : ∀ i, ω.ForeverHonest i → ∃ rr o, recOf ω i (6 * r) = some rr ∧ rr.output = some o)
      (L : Fin P.n) (hL : Event.obs (Obs.elected (7 * (6 * r - 2) + 6) L) ∈ ω.log)
      (hHonest : ω.UncorruptedThrough L (7 * (6 * r - 2) + 6)),
      ∀ i, ω.ForeverHonest i → ∃ rr o, recOf ω i (6 * r) = some rr ∧ rr.output = some o ∧
        ∃ b, o.HoldsTerm (publicCtx P (J P) ω) b) ∧
    (∀ (P : Params) (ζ : ℝ) (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (σ : Type)
      (c : Config P.n CMsg CSt σ),
      ElectNear P ζ E → c.corrupted.card ≤ P.t →
      ENNReal.ofReal (((P.t : ℝ) + 1) / P.n - ζ) ≤ prob (E c.log) {l | l ∉ c.corrupted}) := by sorry

end BeyondDS
